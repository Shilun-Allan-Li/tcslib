## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/pack-r3.md =====

# Gate 07 (Pass–shelat ch. 2–8), round 3: closing check of round 2's findings

**What is audited:** PR [Shilun-Allan-Li/tcslib#210](https://github.com/Shilun-Allan-Li/tcslib/pull/210)
at `eb99dd7bb2d8a270b2ce17a3cf3e1487a65ad0ee`, one commit on round 2's head `3436321ba28042549bead976dc654aab3d661f10`
(docstrings only, three files: `evidence-r3/repair-r3.diff.txt`), base `05fe903fc736ac8036c161ad159dc8bdddcd6ee2`.
This round checks **only** round 2's findings R2-01 – R2-03 (`findings/gate07-eqlemmas-r2-findings.md`,
`resolutions-r2.md`) and the one repair commit. Round 2's other conclusions stand.

**The source** is [PS10], `Pass–Shelat.pdf` at the root of `cryptography/pass-shelat-ch2-4` (SHA-256
`7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`); not needed unless you want it.

- **The deliverable:** **`gate07-eqlemmas-r3-findings.md`**, committed as
  `inbox/gate07-eqlemmas-r3-findings.md` on the exchange branch `exchange/pass-shelat-ch5-8` and pushed
  (protocol: that branch's `README.md`; write only that file, `git pull --rebase` first, never
  force-push, no PR).

## Brief for the auditor

1. **R2-01 (major): F02's consumer.** `evidence-r3/probes/` holds probe files that import
   `HardCoreCollection` from outside it; `R2-01-MAPPING.md` maps each example to its line and log line.
   - The seal (`seal-list.txt`, 42 constants): `PermCollection.glPad`, `Collection.glPad`, every plain
     TCSlib definition reached through their elaborated types and values (`R201Collect.lean`/`.log`),
     the matchers reached, and also `PermCollection.glPad_domEquiv`; `PolyExpr.eval` unsealed (Q1).
   - Pass examples P1–P7 (`R201PassSealed`, `R201PassOpen`): the domain equivalence and its round
     trip; the conjugated permutation equation `perm' = e⁻¹ ∘ (perm_i × id) ∘ e` through `glPad_perm`;
     `perm'` applied and inverted, read through `e`; the field `f' = encD' ∘ perm'`.
   - Controls C1–C5 (`R201ControlOpen` rc 0; `R201ControlSealed` exactly 5 errors): the old readings
     (`z.1`, `(x, r)` as a padded-domain element, `perm'` and P3 by `rfl`, and the statement of
     `glPad_domEquiv_apply`).
   - The maintainer's reading of C5: `glPad_domEquiv_apply` (`e z = z`) is an own-file lemma whose
     statement is well typed only by reading the padded domain as the product; consumers do not
     need it — `glPad_domEquiv` with the `Equiv` lemmas and `glPad_perm` state and prove the
     permutation fact. **Is that the right interface, and do the probes show it?** Say whether F02
     is now fixed.
   The probes were run on the olean tree of this head's replay; their logs are in the folder. If you
   have a Lean toolchain you may re-run them; otherwise review the files and logs as in round 2.
2. **R2-02 (minor):** the six docstrings (`invProb_def`, `predProb_def`, `acceptProb_def`,
   `distAdv_def`, `invProbOpt_def`, `glPadInvFun_eq`) now state the formula. Are the formulas right?
   No statement or proof changed (`evidence-r3/decls-vs-3436321b.tsv` is empty).
3. **R2-03 (minor):** (a) `sorry-compare-vs-05fe903f.tsv` (tool `sorry_compare.py`): only Factoring
   8 → 10 and RSA 9 → 10 against the PR base, total 63 → 66, exactly S1–S3; (b) the extractor
   `decls2.py` keeps a `|` line inside a statement when a `match` is open in it;
   `decls-vs-base.tsv` (367 / 58 / 2) and `decls-vs-r1.tsv` (184 / 55 / 2) regenerated;
   `extractor-fix-diff.txt` shows the only changed row is `GGMRed.queryOf_eq`, now with both arms.
4. **The repair commit**: docstrings only; replay of the 105 modules downstream of the three files
   plus Checks, all rc 0 (`replay-head.log`); `style_lint` and check 8b unchanged
   (`style-lint.log`, `check8b-diff.log`).

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round-2 item: `R2-01: fixed / not resolved — <reason>` (also R2-02, R2-03), and
`F02: fixed / not resolved`. Severity as in rounds 1–2. The gate closes at **0 blockers and 0 majors**.

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/findings/gate07-eqlemmas-r2-findings.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/resolutions-r2.md =====

# Gate 07 (equation-lemma PR #210): round 2 resolutions

- **Round 2:** findings `findings/gate07-eqlemmas-r2-findings.md`, verbatim (delivered by upload; no copy in the exchange
  inbox), SHA-256 `e3cd0b7927f9bb30d743c80499eaa4f86f64bc0bc34340edc98d1193f7a5cfc6`; head `3436321ba28042549bead976dc654aab3d661f10`.
  **Verdict HOLD: 0 blockers, 1 major (R2-01), 2 minors (R2-02, R2-03).** F01 and F03 fixed; F02 not resolved
  (R2-01). The auditor found no counterexample to the new equations, no mathematical change in the restatements,
  and no further rule-10 read in a touched declaration; it reproduced the 547-declaration touched list and the
  (a) = 0 / (b) = 764 classification from the evidence, and checked 781 declaration headers against source.

| Finding | Severity | Resolution |
|---|---|---|
| R2-01 | major | **Confirmed.** No probe consumed `PermCollection.glPad_domEquiv` / `_apply` / `glPad_perm` from another file with `PermCollection.glPad` and `Collection.glPad` sealed; round 1's resolution claimed it. **Repair:** a pass probe that states the conjugated permutation equation on `(P.glPad m henc).D i` through `P.glPad_domEquiv` (and the domain/application lemmas), sealed with `PermCollection.glPad`, `Collection.glPad` and every foreign definition they reach; a paired control that reads the product domain/permutation directly and passes unsealed, fails sealed; source-to-log mapping; at #210's head. F02's disposition is corrected only then. |
| R2-02 | minor | **Confirmed.** `invProb_def`, `predProb_def`, `acceptProb_def`, `distAdv_def`, `invProbOpt_def`, `glPadInvFun_eq`: docstrings get the formula. Docstring-only. |
| R2-03 | minor | **Confirmed.** (1) The `sorry` attestation named the wrong baseline: against the PR base `05fe903f`, Factoring 8 → 10 and RSA 9 → 10 (exactly S1–S3); the round-5 comparison was against `16a7d02d`. A base comparison is regenerated and the wording corrected. (2) `decls.py` stops a statement at a `|` line even inside a statement-level `match` (`GGMRed.queryOf_eq`); the extractor is fixed to continue through match arms before the declaration's `:=`, and the tables are regenerated. |

Round 3 checks R2-01–R2-03 only.

**Repair (2026-11-07):** #210 at `eb99dd7bb2d8a270b2ce17a3cf3e1487a65ad0ee` (one docstring-only commit on `3436321b`). R2-01: sealed consumer probes P1–P7 and controls C1–C5 (`evidence-r3/probes/`, `R2-01-MAPPING.md`); no new equation was needed. `glPad_domEquiv_apply` is an own-file lemma consumers cannot state sealed (C5) and do not need. R2-02: six docstrings. R2-03: `sorry-compare-vs-05fe903f.tsv`; extractor `decls2.py`, tables regenerated (only `queryOf_eq` changes). Round 3 pack: `pack-r3.md`.

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/R2-01-MAPPING.md =====

# R2-01: padded permutation-collection consumer — example → source line → log line

Head: `eb99dd7bb2d8a270b2ce17a3cf3e1487a65ad0ee` (olean tree from the replay in `replay-head.log`).
Files in `probes/`. Each file is elaborated outside `HardCoreCollection.lean`, importing it.

**Seal** (`R201PassSealed.lean`/`R201ControlSealed.lean` line 8; list in `probes/seal-list.txt`): 42 constants made
`local irreducible`: `PermCollection.glPad`, `Collection.glPad`, every plain TCSlib definition reached from their
elaborated types and values (transitively), the matchers reached (`Collection.glPad.match_1/_3`,
`Turing.pairDecode.match_1`, `Turing.Action.apply.match_1`, `Turing.MultiTapeTM.step.match_1`), and in addition
`PermCollection.glPad_domEquiv`. Not sealed: `PolyExpr.eval` (and its matcher), `glNeed` (not reached);
reducible/abbrev, projection and instance constants (`R201Collect.log` lists every reached constant with its kind).
The `*Open.lean` copies are identical without the seal line (lines shifted up by one).

| Example | Claim | Sealed file:line | Sealed log | Open file:line | Open log |
|---|---|---|---|---|---|
| P1 | domain: `P.glPad_domEquiv m henc i : (P.glPad m henc).D i ≃ D_i × {0,1}^L` | PassSealed:17 | `R201PassSealed.log` l.1 `rc=0`, no diagnostic | PassOpen:16 | `R201PassOpen.log` l.1 `rc=0` |
| P2 | domain round trip `e⁻¹ (e z) = z` | PassSealed:21 | same | PassOpen:20 | same |
| P3 | conjugated permutation `perm' = e⁻¹ ∘ (perm_i × id) ∘ e` (`glPad_perm`) | PassSealed:26 | same | PassOpen:25 | same |
| P4 | application: `e (perm' z) = (perm_i (e z).1, (e z).2)` (from `glPad_perm`) | PassSealed:32 | same | PassOpen:31 | same |
| P5 | application: `perm' (e⁻¹ (x, r)) = e⁻¹ (perm_i x, r)` | PassSealed:39 | same | PassOpen:38 | same |
| P6 | application: `perm'⁻¹ (e⁻¹ (x, r)) = e⁻¹ (perm_i⁻¹ x, r)` | PassSealed:46 | same | PassOpen:45 | same |
| P7 | field: `f' i z = encD' i (perm' i z)` (`f_perm` of `P.glPad m henc`) | PassSealed:55 | same | PassOpen:54 | same |
| C1 (↔ P1/P2) | old reading: `z.1 : D_i` for `z : (P.glPad m henc).D i` | ControlSealed:17 | `R201ControlSealed.log` l.1 (17:46, invalid field notation) | ControlOpen:16 | `R201ControlOpen.log` l.1 `rc=0` |
| C2 (↔ P1/P2) | old reading: `(x, r) : (P.glPad m henc).D i` | ControlSealed:20 | l.5 (20:89, type mismatch) | ControlOpen:19 | same |
| C3 (↔ P4) | old reading: `perm' z = (perm_i × id) z` by `rfl` | ControlSealed:24 | l.11 (25:68, application type mismatch) | ControlOpen:23 | same |
| C4 (↔ P3) | old reading: the P3 equation by `rfl` | ControlSealed:29 | l.19 (31:2, type mismatch) | ControlOpen:28 | same |
| C5 (↔ `glPad_domEquiv_apply`) | `e z = z`, the `_apply` statement itself | ControlSealed:35 | l.27 (35:67, type mismatch) | ControlOpen:34 | same |

Sealed control file: 5 errors, one per control (log lines 1, 5, 11, 19, 27). Open control file: `rc=0`, no error.
Pass files: `rc=0`, no diagnostic, sealed and open.

`glPad_domEquiv_apply` (`e z = z`) is a statement about the definition: it is well typed only by reading
`(P.glPad m henc).D i` as the product, so a sealed consumer cannot state it (C5). The consumer interface for
the domain and application is `glPad_domEquiv` with the `Equiv` lemmas (P1, P2) and `glPad_perm` (P3–P6);
no equation had to be added.

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/probes/seal-list.txt =====

attribute [local irreducible] TCSlib.Cryptography.Collection.glPad.match_1 TCSlib.Cryptography.Collection.glPad.match_3 Turing.Action.apply.match_1 Turing.MultiTapeTM.step.match_1 Turing.pairDecode.match_1 Complexity.NUPPT.Uniform Complexity.NUPPT.advInput Complexity.NUPPT.coinLen Complexity.NUPPT.inArg Complexity.NUPPT.inCoins Complexity.NUPPT.inParam Complexity.NUPPT.layout Complexity.NUPPT.ofPolyTime Complexity.NUPPT.ofPolyTimeUniform Complexity.NUPPT.output Complexity.NUPPT.runAt Complexity.NUPPT.timeBound Complexity.PolyTimeComputable Complexity.pairFstD Complexity.pairSndD TCSlib.Cryptography.Collection.glPad TCSlib.Cryptography.Collection.glPadSampleFun TCSlib.Cryptography.Collection.index TCSlib.Cryptography.PermCollection.glPad TCSlib.Cryptography.decodeFin Turing.Action.apply Turing.Cfg.init Turing.Cfg.inputSymbol Turing.Cfg.workTapeSymbols Turing.FinTM.ComputesFunInTime Turing.FinTM.ComputesInTime Turing.MultiTapeTM.ComputesInTimeAndSpace Turing.MultiTapeTM.initCfg Turing.MultiTapeTM.runFrom Turing.MultiTapeTM.spaceUsed Turing.MultiTapeTM.spaceUsedByTape Turing.MultiTapeTM.step Turing.MultiTapeTM.visitedByTapeHead Turing.moveInputPos Turing.pairDecode Turing.pairEncode  TCSlib.Cryptography.PermCollection.glPad_domEquiv

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/probes/R201Collect.lean =====

import TCSlib.Cryptography.Asymptotic.HardCoreCollection

/-! R2-01 seal collector: every TCSlib definition reached (transitively, through types and values,
matchers included) from `PermCollection.glPad` and `Collection.glPad`. Kinds: `def` (plain),
`aux` (matcher / auxiliary), `reducible`, `instance`, `proj`, `irreducible`. Printed one per line as
`SEAL <kind> <name>`; theorems, structures, constructors are walked through their types only. -/

open Lean Meta in
run_cmd do
  let env ← getEnv
  let modNames := env.header.moduleNames
  let isTCS (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some j => (modNames[j.toNat]!).getRoot == `TCSlib
    | none => false
  let roots : Array Name := #[`TCSlib.Cryptography.PermCollection.glPad,
    `TCSlib.Cryptography.Collection.glPad]
  let mut work := roots
  let mut seen : NameSet := {}
  let mut out : Array String := #[]
  while !work.isEmpty do
    let u := work.back!
    work := work.pop
    if seen.contains u then continue
    seen := seen.insert u
    unless isTCS u do continue
    let some ci := env.find? u | continue
    let kind : String := match ci with
      | .defnInfo _ =>
        if isMatcherCore env u then "aux"
        else if env.isProjectionFn u then "proj"
        else if isInstanceCore env u then "instance"
        else if getReducibilityStatusCore env u == .reducible then "reducible"
        else if getReducibilityStatusCore env u == .irreducible then "irreducible"
        else if (u.components.any fun c => c.toString.startsWith "_" ||
            c.toString.startsWith "match_" || c.toString.startsWith "proof_") then "aux"
        else "def"
      | .thmInfo _ => "thm" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec" | .opaqueInfo _ => "opaque" | _ => "other"
    if kind != "thm" && kind != "inductive" && kind != "ctor" && kind != "rec" && kind != "other" then
      out := out.push s!"SEAL {kind} {u}"
    for c in ci.type.getUsedConstants do work := work.push c
    if kind != "thm" then
      match ci with
      | .defnInfo dv => for c in dv.value.getUsedConstants do work := work.push c
      | _ => pure ()
  for l in out.qsort (· < ·) do IO.println l

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/probes/R201Collect.log =====

SEAL aux Complexity.PolyExpr.eval.match_1
SEAL aux TCSlib.Cryptography.Collection.glPad.match_1
SEAL aux TCSlib.Cryptography.Collection.glPad.match_3
SEAL aux Turing.Action.apply.match_1
SEAL aux Turing.MultiTapeTM.step.match_1
SEAL aux Turing.pairDecode.match_1
SEAL def Complexity.NUPPT.Uniform
SEAL def Complexity.NUPPT.advInput
SEAL def Complexity.NUPPT.coinLen
SEAL def Complexity.NUPPT.inArg
SEAL def Complexity.NUPPT.inCoins
SEAL def Complexity.NUPPT.inParam
SEAL def Complexity.NUPPT.layout
SEAL def Complexity.NUPPT.ofPolyTime
SEAL def Complexity.NUPPT.ofPolyTimeUniform
SEAL def Complexity.NUPPT.output
SEAL def Complexity.NUPPT.runAt
SEAL def Complexity.NUPPT.timeBound
SEAL def Complexity.PolyExpr.eval
SEAL def Complexity.PolyTimeComputable
SEAL def Complexity.pairFstD
SEAL def Complexity.pairSndD
SEAL def TCSlib.Cryptography.Collection.glPad
SEAL def TCSlib.Cryptography.Collection.glPadSampleFun
SEAL def TCSlib.Cryptography.Collection.index
SEAL def TCSlib.Cryptography.PermCollection.glPad
SEAL def TCSlib.Cryptography.decodeFin
SEAL def Turing.Action.apply
SEAL def Turing.Cfg.init
SEAL def Turing.Cfg.inputSymbol
SEAL def Turing.Cfg.workTapeSymbols
SEAL def Turing.FinTM.ComputesFunInTime
SEAL def Turing.FinTM.ComputesInTime
SEAL def Turing.MultiTapeTM.ComputesInTimeAndSpace
SEAL def Turing.MultiTapeTM.initCfg
SEAL def Turing.MultiTapeTM.runFrom
SEAL def Turing.MultiTapeTM.spaceUsed
SEAL def Turing.MultiTapeTM.spaceUsedByTape
SEAL def Turing.MultiTapeTM.step
SEAL def Turing.MultiTapeTM.visitedByTapeHead
SEAL def Turing.moveInputPos
SEAL def Turing.pairDecode
SEAL def Turing.pairEncode
SEAL proj Complexity.NUPPT.Ct
SEAL proj Complexity.NUPPT.M
SEAL proj Complexity.NUPPT.advice
SEAL proj Complexity.NUPPT.coins
SEAL proj Complexity.NUPPT.ct
SEAL proj TCSlib.Cryptography.Collection.D
SEAL proj TCSlib.Cryptography.Collection.decD
SEAL proj TCSlib.Cryptography.Collection.encD
SEAL proj TCSlib.Cryptography.Collection.eval
SEAL proj TCSlib.Cryptography.Collection.f
SEAL proj TCSlib.Cryptography.Collection.fintypeD
SEAL proj TCSlib.Cryptography.Collection.gen
SEAL proj TCSlib.Cryptography.Collection.inhabitedD
SEAL proj TCSlib.Cryptography.Collection.sample
SEAL proj TCSlib.Cryptography.PermCollection.perm
SEAL proj TCSlib.Cryptography.PermCollection.toCollection
SEAL proj Turing.Action.inputTape
SEAL proj Turing.Action.output
SEAL proj Turing.Action.state
SEAL proj Turing.Action.workTapes
SEAL proj Turing.Cfg.inputPos
SEAL proj Turing.Cfg.output
SEAL proj Turing.Cfg.state
SEAL proj Turing.Cfg.workTapePos
SEAL proj Turing.Cfg.workTapes
SEAL proj Turing.FinTM.State
SEAL proj Turing.FinTM.k
SEAL proj Turing.FinTM.tm
SEAL proj Turing.MultiTapeTM.q₀
SEAL proj Turing.MultiTapeTM.tr
SEAL reducible Complexity.NUPPT.Coins
SEAL reducible Complexity.PolyExpr.below
SEAL reducible Complexity.PolyExpr.brecOn
SEAL reducible Complexity.PolyExpr.brecOn.go
SEAL reducible Complexity.PolyExpr.casesOn
rc=0

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/probes/R201PassSealed.lean =====

import TCSlib.Cryptography.Asymptotic.HardCoreCollection

set_option autoImplicit false

open Complexity Turing TCSlib.Cryptography

-- SEAL-LINE
attribute [local irreducible] TCSlib.Cryptography.Collection.glPad.match_1 TCSlib.Cryptography.Collection.glPad.match_3 Turing.Action.apply.match_1 Turing.MultiTapeTM.step.match_1 Turing.pairDecode.match_1 Complexity.NUPPT.Uniform Complexity.NUPPT.advInput Complexity.NUPPT.coinLen Complexity.NUPPT.inArg Complexity.NUPPT.inCoins Complexity.NUPPT.inParam Complexity.NUPPT.layout Complexity.NUPPT.ofPolyTime Complexity.NUPPT.ofPolyTimeUniform Complexity.NUPPT.output Complexity.NUPPT.runAt Complexity.NUPPT.timeBound Complexity.PolyTimeComputable Complexity.pairFstD Complexity.pairSndD TCSlib.Cryptography.Collection.glPad TCSlib.Cryptography.Collection.glPadSampleFun TCSlib.Cryptography.Collection.index TCSlib.Cryptography.PermCollection.glPad TCSlib.Cryptography.decodeFin Turing.Action.apply Turing.Cfg.init Turing.Cfg.inputSymbol Turing.Cfg.workTapeSymbols Turing.FinTM.ComputesFunInTime Turing.FinTM.ComputesInTime Turing.MultiTapeTM.ComputesInTimeAndSpace Turing.MultiTapeTM.initCfg Turing.MultiTapeTM.runFrom Turing.MultiTapeTM.spaceUsed Turing.MultiTapeTM.spaceUsedByTape Turing.MultiTapeTM.step Turing.MultiTapeTM.visitedByTapeHead Turing.moveInputPos Turing.pairDecode Turing.pairEncode  TCSlib.Cryptography.PermCollection.glPad_domEquiv

variable (P : PermCollection) (m : PolyExpr)
  (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
  (i : List Bool)

/-! ## Pass: a consumer of the padded permutation collection's domain/permutation interface -/

-- P1 (domain): the published domain of `(P.glPad m henc).D i` is `D_i × {0,1}^L`.
example : (P.glPad m henc).D i ≃ P.D i × (Fin (P.encD i default).length → Bool) :=
  P.glPad_domEquiv m henc i

-- P2 (domain, round trip): elements of the padded domain are read and rebuilt through `e`.
example (z : (P.glPad m henc).D i) :
    (P.glPad_domEquiv m henc i).symm (P.glPad_domEquiv m henc i z) = z :=
  (P.glPad_domEquiv m henc i).symm_apply_apply z

-- P3 (permutation): the conjugated permutation equation `perm' = e⁻¹ ∘ (perm_i × id) ∘ e`.
example : (P.glPad m henc).perm i = ((P.glPad_domEquiv m henc i).trans
    ((P.perm i).prodCongr (Equiv.refl _))).trans (P.glPad_domEquiv m henc i).symm :=
  P.glPad_perm m henc i

-- P4 (application, forward): read through `e`, `perm'` is `perm_i` on the first component and
-- the identity on the padding.
example (z : (P.glPad m henc).D i) :
    P.glPad_domEquiv m henc i ((P.glPad m henc).perm i z) =
      (P.perm i (P.glPad_domEquiv m henc i z).1, (P.glPad_domEquiv m henc i z).2) := by
  rw [P.glPad_perm m henc i, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.trans_apply,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]

-- P5 (application, backward): on an element built from `(x, r)` through `e⁻¹`.
example (x : P.D i) (r : Fin (P.encD i default).length → Bool) :
    (P.glPad m henc).perm i ((P.glPad_domEquiv m henc i).symm (x, r)) =
      (P.glPad_domEquiv m henc i).symm (P.perm i x, r) := by
  rw [P.glPad_perm m henc i, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]

-- P6 (application, inverse permutation): `perm'⁻¹ = e⁻¹ ∘ (perm_i⁻¹ × id) ∘ e`.
example (x : P.D i) (r : Fin (P.encD i default).length → Bool) :
    ((P.glPad m henc).perm i).symm ((P.glPad_domEquiv m henc i).symm (x, r)) =
      (P.glPad_domEquiv m henc i).symm ((P.perm i).symm x, r) := by
  rw [P.glPad_perm m henc i, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.refl_symm, Equiv.refl_apply]

-- P7 (field): the padded collection's function is its encoding after its permutation
-- (`PermCollection.f_perm` of `P.glPad m henc`), with the permutation read as in P4.
example (z : (P.glPad m henc).D i) :
    (P.glPad m henc).f i z = (P.glPad m henc).encD i ((P.glPad m henc).perm i z) :=
  (P.glPad m henc).f_perm i z

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/probes/R201PassSealed.log =====

rc=0

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/probes/R201PassOpen.lean =====

import TCSlib.Cryptography.Asymptotic.HardCoreCollection

set_option autoImplicit false

open Complexity Turing TCSlib.Cryptography

-- SEAL-LINE

variable (P : PermCollection) (m : PolyExpr)
  (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
  (i : List Bool)

/-! ## Pass: a consumer of the padded permutation collection's domain/permutation interface -/

-- P1 (domain): the published domain of `(P.glPad m henc).D i` is `D_i × {0,1}^L`.
example : (P.glPad m henc).D i ≃ P.D i × (Fin (P.encD i default).length → Bool) :=
  P.glPad_domEquiv m henc i

-- P2 (domain, round trip): elements of the padded domain are read and rebuilt through `e`.
example (z : (P.glPad m henc).D i) :
    (P.glPad_domEquiv m henc i).symm (P.glPad_domEquiv m henc i z) = z :=
  (P.glPad_domEquiv m henc i).symm_apply_apply z

-- P3 (permutation): the conjugated permutation equation `perm' = e⁻¹ ∘ (perm_i × id) ∘ e`.
example : (P.glPad m henc).perm i = ((P.glPad_domEquiv m henc i).trans
    ((P.perm i).prodCongr (Equiv.refl _))).trans (P.glPad_domEquiv m henc i).symm :=
  P.glPad_perm m henc i

-- P4 (application, forward): read through `e`, `perm'` is `perm_i` on the first component and
-- the identity on the padding.
example (z : (P.glPad m henc).D i) :
    P.glPad_domEquiv m henc i ((P.glPad m henc).perm i z) =
      (P.perm i (P.glPad_domEquiv m henc i z).1, (P.glPad_domEquiv m henc i z).2) := by
  rw [P.glPad_perm m henc i, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.trans_apply,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]

-- P5 (application, backward): on an element built from `(x, r)` through `e⁻¹`.
example (x : P.D i) (r : Fin (P.encD i default).length → Bool) :
    (P.glPad m henc).perm i ((P.glPad_domEquiv m henc i).symm (x, r)) =
      (P.glPad_domEquiv m henc i).symm (P.perm i x, r) := by
  rw [P.glPad_perm m henc i, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]

-- P6 (application, inverse permutation): `perm'⁻¹ = e⁻¹ ∘ (perm_i⁻¹ × id) ∘ e`.
example (x : P.D i) (r : Fin (P.encD i default).length → Bool) :
    ((P.glPad m henc).perm i).symm ((P.glPad_domEquiv m henc i).symm (x, r)) =
      (P.glPad_domEquiv m henc i).symm ((P.perm i).symm x, r) := by
  rw [P.glPad_perm m henc i, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.refl_symm, Equiv.refl_apply]

-- P7 (field): the padded collection's function is its encoding after its permutation
-- (`PermCollection.f_perm` of `P.glPad m henc`), with the permutation read as in P4.
example (z : (P.glPad m henc).D i) :
    (P.glPad m henc).f i z = (P.glPad m henc).encD i ((P.glPad m henc).perm i z) :=
  (P.glPad m henc).f_perm i z

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/probes/R201PassOpen.log =====

rc=0

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/probes/R201ControlSealed.lean =====

import TCSlib.Cryptography.Asymptotic.HardCoreCollection

set_option autoImplicit false

open Complexity Turing TCSlib.Cryptography

-- SEAL-LINE
attribute [local irreducible] TCSlib.Cryptography.Collection.glPad.match_1 TCSlib.Cryptography.Collection.glPad.match_3 Turing.Action.apply.match_1 Turing.MultiTapeTM.step.match_1 Turing.pairDecode.match_1 Complexity.NUPPT.Uniform Complexity.NUPPT.advInput Complexity.NUPPT.coinLen Complexity.NUPPT.inArg Complexity.NUPPT.inCoins Complexity.NUPPT.inParam Complexity.NUPPT.layout Complexity.NUPPT.ofPolyTime Complexity.NUPPT.ofPolyTimeUniform Complexity.NUPPT.output Complexity.NUPPT.runAt Complexity.NUPPT.timeBound Complexity.PolyTimeComputable Complexity.pairFstD Complexity.pairSndD TCSlib.Cryptography.Collection.glPad TCSlib.Cryptography.Collection.glPadSampleFun TCSlib.Cryptography.Collection.index TCSlib.Cryptography.PermCollection.glPad TCSlib.Cryptography.decodeFin Turing.Action.apply Turing.Cfg.init Turing.Cfg.inputSymbol Turing.Cfg.workTapeSymbols Turing.FinTM.ComputesFunInTime Turing.FinTM.ComputesInTime Turing.MultiTapeTM.ComputesInTimeAndSpace Turing.MultiTapeTM.initCfg Turing.MultiTapeTM.runFrom Turing.MultiTapeTM.spaceUsed Turing.MultiTapeTM.spaceUsedByTape Turing.MultiTapeTM.step Turing.MultiTapeTM.visitedByTapeHead Turing.moveInputPos Turing.pairDecode Turing.pairEncode  TCSlib.Cryptography.PermCollection.glPad_domEquiv

variable (P : PermCollection) (m : PolyExpr)
  (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
  (i : List Bool)

/-! ## Controls: the old reading (product domain and permutation read directly) -/

-- C1 (domain read as a product): the first component of an element of the padded domain.
example (z : (P.glPad m henc).D i) : P.D i := z.1

-- C2 (domain read as a product): an element of the padded domain built as a pair.
example (x : P.D i) (r : Fin (P.encD i default).length → Bool) : (P.glPad m henc).D i := (x, r)

-- C3 (permutation read directly): `perm'` is `perm_i × id` applied to the padded element
-- read as a pair, by unfolding.
example (z : (P.glPad m henc).D i) :
    (P.glPad m henc).perm i z = (P.perm i).prodCongr (Equiv.refl _) z :=
  rfl

-- C4 (permutation equation by unfolding): the conjugation equation of P3, proved by `rfl`.
example : (P.glPad m henc).perm i = ((P.glPad_domEquiv m henc i).trans
    ((P.perm i).prodCongr (Equiv.refl _))).trans (P.glPad_domEquiv m henc i).symm :=
  rfl

-- C5 (`glPad_domEquiv_apply`, the identity on the definition): `e z = z` is well typed only by
-- reading `(P.glPad m henc).D i` as the product.
example (z : (P.glPad m henc).D i) : P.glPad_domEquiv m henc i z = z :=
  P.glPad_domEquiv_apply m henc i z

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/probes/R201ControlSealed.log =====

/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/e1/r2fix/probes/R201ControlSealed.lean:17:46: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  z
has type
  (P.glPad m henc).toCollection.1 i
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/e1/r2fix/probes/R201ControlSealed.lean:20:89: error: Type mismatch
  (x, r)
has type
  P.D i × (Fin (P.encD i default).length → Bool)
but is expected to have type
  (P.glPad m henc).D i
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/e1/r2fix/probes/R201ControlSealed.lean:25:68: error: Application type mismatch: The argument
  z
has type
  (P.glPad m henc).D i
but is expected to have type
  P.D i × ?m.9
in the application
  ((P.perm i).prodCongr (Equiv.refl ?m.9)) z
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/e1/r2fix/probes/R201ControlSealed.lean:31:2: error: Type mismatch
  rfl
has type
  ?m.19 = ?m.19
but is expected to have type
  (P.glPad m henc).perm i =
    ((P.glPad_domEquiv m henc i).trans ((P.perm i).prodCongr (Equiv.refl (Fin (P.encD i default).length → Bool)))).trans
      (P.glPad_domEquiv m henc i).symm
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/e1/r2fix/probes/R201ControlSealed.lean:35:67: error: Type mismatch
  z
has type
  (P.glPad m henc).D i
but is expected to have type
  P.D i × (Fin (P.encD i default).length → Bool)
rc=1

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/probes/R201ControlOpen.lean =====

import TCSlib.Cryptography.Asymptotic.HardCoreCollection

set_option autoImplicit false

open Complexity Turing TCSlib.Cryptography

-- SEAL-LINE

variable (P : PermCollection) (m : PolyExpr)
  (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
  (i : List Bool)

/-! ## Controls: the old reading (product domain and permutation read directly) -/

-- C1 (domain read as a product): the first component of an element of the padded domain.
example (z : (P.glPad m henc).D i) : P.D i := z.1

-- C2 (domain read as a product): an element of the padded domain built as a pair.
example (x : P.D i) (r : Fin (P.encD i default).length → Bool) : (P.glPad m henc).D i := (x, r)

-- C3 (permutation read directly): `perm'` is `perm_i × id` applied to the padded element
-- read as a pair, by unfolding.
example (z : (P.glPad m henc).D i) :
    (P.glPad m henc).perm i z = (P.perm i).prodCongr (Equiv.refl _) z :=
  rfl

-- C4 (permutation equation by unfolding): the conjugation equation of P3, proved by `rfl`.
example : (P.glPad m henc).perm i = ((P.glPad_domEquiv m henc i).trans
    ((P.perm i).prodCongr (Equiv.refl _))).trans (P.glPad_domEquiv m henc i).symm :=
  rfl

-- C5 (`glPad_domEquiv_apply`, the identity on the definition): `e z = z` is well typed only by
-- reading `(P.glPad m henc).D i` as the product.
example (z : (P.glPad m henc).D i) : P.glPad_domEquiv m henc i z = z :=
  P.glPad_domEquiv_apply m henc i z

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/probes/R201ControlOpen.log =====

rc=0

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/probes/run.sh =====

#!/usr/bin/env bash
# run.sh <file.lean>: elaborate a probe against the e1 (head) olean tree, no olean output
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
ROOT=$SP/wt-e1; LP=$SP/e1-oleans
for d in "$ROOT"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
export LEAN_PATH="$LP" PATH="$HOME/.elan/bin:$PATH"
F=$(readlink -f "$1"); cd "$ROOT" && lean "$F"; echo "rc=$?"

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/repair-r3.diff.txt =====

diff --git a/TCSlib/Cryptography/Asymptotic/Adversary.lean b/TCSlib/Cryptography/Asymptotic/Adversary.lean
index 84c089bf..34833468 100644
--- a/TCSlib/Cryptography/Asymptotic/Adversary.lean
+++ b/TCSlib/Cryptography/Asymptotic/Adversary.lean
@@ -177,7 +177,9 @@ noncomputable def invProbOpt {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : 
     (A : β → ρ → Option α) : ℝ :=
   uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1
 
-/-- The defining equation of `invProbOpt`. -/
+/-- The defining equation of `invProbOpt`:
+`invProbOpt f A = Pr_{(x, r)}[∃ x', A(f x, r) = some x' ∧ f x' = f x]`, over uniform
+`(x, r) ∈ α × ρ`. -/
 theorem invProbOpt_def {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
     (A : β → ρ → Option α) :
     invProbOpt f A = uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1 := rfl
diff --git a/TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean b/TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean
index 4c942110..79c41c5a 100644
--- a/TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean
+++ b/TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean
@@ -979,7 +979,7 @@ def glPadInvFun (T : TrapdoorCollection) (z : List Bool) : List Bool :=
       (NUPPT.inCoins z)))
     (pairSndD (pairSndD (NUPPT.inArg z)))
 
-/-- The defining equation of `glPadInvFun`. -/
+/-- `glPadInvFun T z = ⟨Inv(1^n, ⟨t, y⟩; s), r⟩` on `z = ⟨⟨⟨1^n, ⟨t, ⟨y, r⟩⟩⟩, []⟩, s⟩`. -/
 theorem glPadInvFun_eq (T : TrapdoorCollection) (z : List Bool) : glPadInvFun T z = pairEncode
     (T.inv.output (NUPPT.layout (NUPPT.inParam z)
       (pairEncode (pairFstD (NUPPT.inArg z)) (pairFstD (pairSndD (NUPPT.inArg z)))) []
diff --git a/TCSlib/Cryptography/Foundations/Experiments.lean b/TCSlib/Cryptography/Foundations/Experiments.lean
index 6f044604..fc8fe103 100644
--- a/TCSlib/Cryptography/Foundations/Experiments.lean
+++ b/TCSlib/Cryptography/Foundations/Experiments.lean
@@ -83,19 +83,22 @@ noncomputable def distAdv (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Boo
 Published so that other layers (the `Games` bridges) read the experiments through stated
 equations rather than through their bodies. -/
 
-/-- The defining equation of `invProb`. -/
+/-- The defining equation of `invProb`: `invProb f A = Pr_{(x, r)}[f(A(f x, r)) = f x]`, over
+uniform `(x, r) ∈ α × ρ`. -/
 theorem invProb_def (f : α → β) (A : β → ρ → α) :
     invProb f A = uprob fun z : α × ρ => f (A (f z.1) z.2) = f z.1 := rfl
 
-/-- The defining equation of `predProb`. -/
+/-- The defining equation of `predProb`: `predProb f B A = Pr_{(x, r)}[A(f x, r) = B x]`, over
+uniform `(x, r) ∈ α × ρ`. -/
 theorem predProb_def (f : α → β) (B : α → Bool) (A : β → ρ → Bool) :
     predProb f B A = uprob fun z : α × ρ => A (f z.1) z.2 = B z.1 := rfl
 
-/-- The defining equation of `acceptProb`. -/
+/-- The defining equation of `acceptProb`: `acceptProb X D = Pr_{(s, r)}[D(X s, r) = 1]`, over
+uniform `(s, r) ∈ σ × ρ`. -/
 theorem acceptProb_def (X : σ → γ) (D : γ → ρ → Bool) :
     acceptProb X D = uprob fun z : σ × ρ => D (X z.1) z.2 = true := rfl
 
-/-- The defining equation of `distAdv`. -/
+/-- The defining equation of `distAdv`: `distAdv X Y D = |acceptProb X D - acceptProb Y D|`. -/
 theorem distAdv_def (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) :
     distAdv X Y D = |acceptProb X D - acceptProb Y D| := rfl
 

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/sorry-compare-vs-05fe903f.tsv =====

file	base_sorry_tokens	head_sorry_tokens	head_replay_sorry_warnings
TCSlib/Complexity/ClassNP/PolyTimePairing.lean	0	0	-
TCSlib/Complexity/Randomized/Closure.lean	0	0	-
TCSlib/Complexity/Randomized/NonUniform.lean	1	1	-
TCSlib/Complexity/Randomized/PPT.lean	0	0	-
TCSlib/Complexity/Randomized/PolyExpr.lean	0	0	-
TCSlib/Cryptography/Asymptotic/Adversary.lean	0	0	0
TCSlib/Cryptography/Asymptotic/BlockEncryptor.lean	0	0	0
TCSlib/Cryptography/Asymptotic/Collections.lean	0	0	0
TCSlib/Cryptography/Asymptotic/CollectionsHelpers.lean	0	0	0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas.lean	0	0	0
TCSlib/Cryptography/Asymptotic/Encryption.lean	0	0	0
TCSlib/Cryptography/Asymptotic/Ensembles.lean	0	0	0
TCSlib/Cryptography/Asymptotic/GGMReduction.lean	0	0	0
TCSlib/Cryptography/Asymptotic/GGMReductionEval.lean	0	0	0
TCSlib/Cryptography/Asymptotic/HardCore.lean	0	0	0
TCSlib/Cryptography/Asymptotic/HardCoreClaims.lean	0	0	0
TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean	0	0	0
TCSlib/Cryptography/Asymptotic/HardCoreGL.lean	0	0	0
TCSlib/Cryptography/Asymptotic/HardCoreGLColl.lean	0	0	0
TCSlib/Cryptography/Asymptotic/HardCoreGLFamily.lean	0	0	0
TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean	0	0	0
TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean	0	0	0
TCSlib/Cryptography/Asymptotic/OneWay.lean	0	0	0
TCSlib/Cryptography/Asymptotic/OneWayYao.lean	0	0	0
TCSlib/Cryptography/Asymptotic/PublicKey.lean	0	0	0
TCSlib/Cryptography/Asymptotic/PublicKeyLemmas.lean	0	0	0
TCSlib/Cryptography/Asymptotic/Sampling.lean	0	0	0
TCSlib/Cryptography/Asymptotic/Universal.lean	1	1	1
TCSlib/Cryptography/Asymptotic/UniversalPadding.lean	1	1	1
TCSlib/Cryptography/Candidates/Arithmetic.lean	0	0	0
TCSlib/Cryptography/Candidates/Concrete.lean	1	1	1
TCSlib/Cryptography/Candidates/DiscreteLog.lean	6	6	6
TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean	7	7	7
TCSlib/Cryptography/Candidates/ElGamal.lean	7	7	7
TCSlib/Cryptography/Candidates/Factoring.lean	8	10	10
TCSlib/Cryptography/Candidates/RSA.lean	9	10	10
TCSlib/Cryptography/Candidates/Rabin.lean	19	19	19
TCSlib/Cryptography/Foundations/Experiments.lean	0	0	0
TCSlib/Cryptography/Foundations/Negligible.lean	0	0	-
TCSlib/Cryptography/Foundations/Probability.lean	0	0	-
TCSlib/Cryptography/HardcoreBit/Basic.lean	0	0	-
TCSlib/Cryptography/HardcoreBit/GoldreichLevin.lean	0	0	0
TCSlib/Cryptography/HardcoreBit/InnerProduct.lean	0	0	0
TCSlib/Cryptography/HardcoreBit/PairwiseIndependence.lean	0	0	-
TCSlib/Cryptography/HardcoreBit/ThreeQuarters.lean	0	0	0
TCSlib/Cryptography/NumberTheory/Primality.lean	0	0	0
TCSlib/Cryptography/OneWayFunctions/Amplification.lean	0	0	0
TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean	0	0	0
TCSlib/Cryptography/Pseudorandom/Generators.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/Commitment.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/Defs.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/Encoding.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/Encryption.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean	0	0	-
TCSlib/Cryptography/ZeroKnowledge/NP.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean	2	2	2
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean	0	0	0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean	1	1	1
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean	0	0	0
TCSlib/InformationTheory/StatisticalDistance.lean	0	0	-

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/sorry_compare.py =====

"""sorry_compare.py <worktree> <base> <head-rev> <replay-log-dir> <files...>: executable `sorry` tokens
(block/line comments and string literals removed, nested `/- -/` handled) per file at <base> and at
<head-rev>, and the head replay's `declaration uses 'sorry'` warnings where the module was replayed."""
import re, subprocess, sys, os
WT, BASE, HEAD, LOGS = sys.argv[1:5]
def strip(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"': j += 2 if src[j] == '\\' else 1
            i = j + 1; continue
        out.append(src[i]); i += 1
    return ''.join(out)
def count(rev, f):
    p = subprocess.run(['git', '-C', WT, 'show', f'{rev}:{f}'], capture_output=True, text=True)
    return len(re.findall(r'(?<![\w.])sorry(?![\w])', strip(p.stdout))) if p.returncode == 0 else 'absent'
print('file\tbase_sorry_tokens\thead_sorry_tokens\thead_replay_sorry_warnings')
for f in sys.argv[5:]:
    log = os.path.join(LOGS, f[:-5].replace('/', '_') + '.log')
    w = open(log).read().count("declaration uses 'sorry'") if os.path.exists(log) else '-'
    print(f'{f}\t{count(BASE, f)}\t{count(HEAD, f)}\t{w}')

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/decls2.py =====

"""decls2.py <root> <base-rev> <file>...: public declarations (full name -> (kind, line, normalized
statement)) at <base-rev> and in the working tree; prints added / removed / changed as TSV.
decls2 (gate 07 R2-03): a line starting with `|` that follows a `match … with` opened in the statement
(before the declaration's top-level `:=`) is a match arm of the statement and does not end it; only
arms of an equation-compiler definition (no `match` in the statement), the `:=`, or the next
declaration end a statement."""
import sys, re, subprocess
root, base = sys.argv[1], sys.argv[2]
files = sys.argv[3:]
KW = r'(theorem|lemma|def|abbrev|structure|inductive|instance|class)'
def strip(src):
    src = re.sub(r'/-.*?-/', lambda m: '\n' * m.group(0).count('\n'), src, flags=re.S)
    return re.sub(r'--[^\n]*', '', src)
def decls(src):
    lines = strip(src).split('\n')
    out, ns, i = {}, [], 0
    while i < len(lines):
        l = lines[i]
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: ns.append(m.group(1)); i += 1; continue
        m = re.match(r'^end\s+(\S+)\s*$', l)
        if m and ns and ns[-1] == m.group(1): ns.pop(); i += 1; continue
        m = re.match(r'^(@\[[^\]]*\]\s*)?((?:private|protected|noncomputable|nonrec)\s+)*' + KW +
                     r'\s+([^\s(:{\[]+)', l)
        if m and not re.search(r'\bprivate\b', l.split(m.group(3))[0]):
            name = m.group(4)
            full = name[len('_root_.'):] if name.startswith('_root_.') else '.'.join(ns + [name])
            def cut(t):
                d = 0
                for k, ch in enumerate(t):
                    if ch in '([{⟨': d += 1
                    elif ch in ')]}⟩': d -= 1
                    elif d == 0 and t.startswith(':=', k): return t[:k]
                    elif d == 0 and re.match(r'\bwhere\b', t[k:]) and (k == 0 or not t[k-1].isalnum()):
                        return t[:k]
                return None
            j, buf = i, []
            while j < len(lines):
                buf.append(lines[j])
                c = cut(' '.join(buf))
                if c is not None or (j > i and lines[j+1:j+2] and re.match(r'^\s*\|[^|\n]*=>', lines[j+1])
                                     and not re.search(r'\bmatch\b', ' '.join(buf))):
                    break
                j += 1
            t = ' '.join(buf)
            c = cut(t)
            t = c if c is not None else t
            t = re.sub(r'^@\[[^\]]*\]\s*', '', t.strip())
            out[full] = (m.group(3), i + 1, re.sub(r'\s+', ' ', t).strip())
            i = j + 1; continue
        i += 1
    return out
for f in files:
    old = subprocess.run(['git', 'show', f'{base}:{f}'], cwd=root, capture_output=True,
                         text=True).stdout
    new = open(f'{root}/{f}', encoding='utf-8').read()
    a, b = decls(old) if old else {}, decls(new)
    for n in sorted(set(a) | set(b)):
        if n in a and n not in b:
            print(f"REMOVED\t{f}:{a[n][1]}\t{n}\t{a[n][0]}\t{a[n][2]}")
        elif n in b and n not in a:
            print(f"ADDED\t{f}:{b[n][1]}\t{n}\t{b[n][0]}\t{b[n][2]}")
        elif a[n][2] != b[n][2]:
            print(f"CHANGED\t{f}:{a[n][1]}->{b[n][1]}\t{n}\t{b[n][0]}\t{a[n][2]}\t=>\t{b[n][2]}")

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/extractor-fix-diff.txt =====

== decls-vs-base (old extractor < / > fixed extractor)
< ADDED	TCSlib/Cryptography/Asymptotic/GGMReduction.lean:97	TCSlib.Cryptography.GGMRed.queryOf_eq	theorem	theorem queryOf_eq (ℓ₁ : ℕ) (w : List Bool) : queryOf ℓ₁ w = match pairDecode w with
> ADDED	TCSlib/Cryptography/Asymptotic/GGMReduction.lean:97	TCSlib.Cryptography.GGMRed.queryOf_eq	theorem	theorem queryOf_eq (ℓ₁ : ℕ) (w : List Bool) : queryOf ℓ₁ w = match pairDecode w with | some ([false], x) => decodeFin ℓ₁ x | _ => none
== decls-vs-r1 (old extractor < / > fixed extractor)

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/decls-vs-3436321b.tsv =====



## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/decls-vs-base.tsv =====

ADDED	TCSlib/Complexity/ClassNP/PolyTimePairing.lean:212	Complexity.pairFstD_eq	theorem	theorem pairFstD_eq (z : List Bool) : pairFstD z = ((pairDecode z).map Prod.fst).getD []
ADDED	TCSlib/Complexity/ClassNP/PolyTimePairing.lean:219	Complexity.pairFstD_of_pairDecode_eq_none	theorem	theorem pairFstD_of_pairDecode_eq_none {z : List Bool} (h : pairDecode z = none) : pairFstD z = []
ADDED	TCSlib/Complexity/ClassNP/PolyTimePairing.lean:215	Complexity.pairSndD_eq	theorem	theorem pairSndD_eq (z : List Bool) : pairSndD z = ((pairDecode z).map Prod.snd).getD []
ADDED	TCSlib/Complexity/ClassNP/PolyTimePairing.lean:226	Complexity.pairSndD_of_pairDecode_eq_none	theorem	theorem pairSndD_of_pairDecode_eq_none {z : List Bool} (h : pairDecode z = none) : pairSndD z = []
ADDED	TCSlib/Complexity/Randomized/Closure.lean:119	Complexity.NUPPT.inAdvice_eq	theorem	theorem inAdvice_eq (z : List Bool) : inAdvice z = pairSndD (pairFstD z)
ADDED	TCSlib/Complexity/Randomized/Closure.lean:116	Complexity.NUPPT.inArg_eq	theorem	theorem inArg_eq (z : List Bool) : inArg z = pairSndD (pairFstD (pairFstD z))
ADDED	TCSlib/Complexity/Randomized/Closure.lean:122	Complexity.NUPPT.inCoins_eq	theorem	theorem inCoins_eq (z : List Bool) : inCoins z = pairSndD z
ADDED	TCSlib/Complexity/Randomized/Closure.lean:113	Complexity.NUPPT.inParam_eq	theorem	theorem inParam_eq (z : List Bool) : inParam z = pairFstD (pairFstD (pairFstD z))
ADDED	TCSlib/Complexity/Randomized/Closure.lean:109	Complexity.NUPPT.layout_eq	theorem	theorem layout_eq (u y α r : List Bool) : layout u y α r = pairEncode (pairEncode (pairEncode u y) α) r
REMOVED	TCSlib/Complexity/Randomized/NonUniform.lean:94	Complexity.NUPPT.Uniform.advice_eq	theorem	theorem Uniform.advice_eq {A : NUPPT} (h : A.Uniform) (n : ℕ) : A.advice n = []
REMOVED	TCSlib/Complexity/Randomized/NonUniform.lean:112	Complexity.NUPPT.uniform_iff	theorem	theorem uniform_iff : A.Uniform ↔ ∀ n, A.advice n = []
ADDED	TCSlib/Complexity/Randomized/PPT.lean:289	Complexity.NUPPT.Uniform.advice_eq	theorem	theorem Uniform.advice_eq {A : NUPPT} (h : A.Uniform) (n : ℕ) : A.advice n = []
ADDED	TCSlib/Complexity/Randomized/PPT.lean:206	Complexity.NUPPT.advInput_eq	theorem	theorem advInput_eq (n : ℕ) (y : List Bool) : advInput n y = pairEncode (List.replicate n true) y
ADDED	TCSlib/Complexity/Randomized/PPT.lean:163	Complexity.NUPPT.coinLen_eq	theorem	theorem coinLen_eq (n : ℕ) : A.coinLen n = A.coins.eval n
ADDED	TCSlib/Complexity/Randomized/PPT.lean:241	Complexity.NUPPT.coinsCongr	def	def coinsCongr {A B : NUPPT} (h : A.coins = B.coins) (n : ℕ) : A.Coins n ≃ B.Coins n
ADDED	TCSlib/Complexity/Randomized/PPT.lean:245	Complexity.NUPPT.coinsCongr_ofFn	theorem	theorem coinsCongr_ofFn {A B : NUPPT} (h : A.coins = B.coins) (n : ℕ) (r : A.Coins n) : List.ofFn (coinsCongr h n r) = List.ofFn r
ADDED	TCSlib/Complexity/Randomized/PPT.lean:259	Complexity.NUPPT.coinsEquivPoly	def	def coinsEquivPoly {A : NUPPT} {c : PolyExpr} (h : A.coins = c) (n : ℕ) : A.Coins n ≃ (Fin (c.eval n) → Bool)
ADDED	TCSlib/Complexity/Randomized/PPT.lean:265	Complexity.NUPPT.coinsEquivPoly_ofFn	theorem	theorem coinsEquivPoly_ofFn {A : NUPPT} {c : PolyExpr} (h : A.coins = c) (n : ℕ) (r : A.Coins n) : List.ofFn (coinsEquivPoly h n r) = List.ofFn r
ADDED	TCSlib/Complexity/Randomized/PPT.lean:271	Complexity.NUPPT.coinsEquivPoly_symm_ofFn	theorem	theorem coinsEquivPoly_symm_ofFn {A : NUPPT} {c : PolyExpr} (h : A.coins = c) (n : ℕ) (w : Fin (c.eval n) → Bool) : List.ofFn ((coinsEquivPoly h n).symm w) = List.ofFn w
ADDED	TCSlib/Complexity/Randomized/PPT.lean:348	Complexity.NUPPT.coinsEquiv_ofPolyTime	def	noncomputable def coinsEquiv_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f) (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) (n : ℕ) : (ofPolyTime hf coins adv advice hα).Coins n ≃ (Fin (coins.eval n) → Bool)
ADDED	TCSlib/Complexity/Randomized/PPT.lean:398	Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform	def	noncomputable def coinsEquiv_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f) (coins : PolyExpr) (n : ℕ) : (ofPolyTimeUniform hf coins).Coins n ≃ (Fin (coins.eval n) → Bool)
ADDED	TCSlib/Complexity/Randomized/PPT.lean:403	Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn	theorem	theorem coinsEquiv_ofPolyTimeUniform_ofFn {f : List Bool → List Bool} (hf : PolyTimeComputable f) (coins : PolyExpr) (n : ℕ) (r : (ofPolyTimeUniform hf coins).Coins n) : List.ofFn (coinsEquiv_ofPolyTimeUniform hf coins n r) = List.ofFn r
ADDED	TCSlib/Complexity/Randomized/PPT.lean:354	Complexity.NUPPT.coinsEquiv_ofPolyTime_ofFn	theorem	theorem coinsEquiv_ofPolyTime_ofFn {f : List Bool → List Bool} (hf : PolyTimeComputable f) (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) (n : ℕ) (r : (ofPolyTime hf coins adv advice hα).Coins n) : List.ofFn (coinsEquiv_ofPolyTime hf coins adv advice hα n r) = List.ofFn r
ADDED	TCSlib/Complexity/Randomized/PPT.lean:230	Complexity.NUPPT.runAtL_eq	theorem	theorem runAtL_eq (n : ℕ) (y r : List Bool) : A.runAtL n y r = A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)
ADDED	TCSlib/Complexity/Randomized/PPT.lean:251	Complexity.NUPPT.runAt_coinsCongr	theorem	theorem runAt_coinsCongr {A B : NUPPT} (h : A.coins = B.coins) (n : ℕ) (y : List Bool) (r : A.Coins n) : B.runAt n y (coinsCongr h n r) = B.runAtL n y (List.ofFn r)
ADDED	TCSlib/Complexity/Randomized/PPT.lean:286	Complexity.NUPPT.uniform_iff	theorem	theorem uniform_iff : A.Uniform ↔ ∀ n, A.advice n = []
ADDED	TCSlib/Cryptography/Asymptotic/Adversary.lean:137	Complexity.NUPPT.distinguisherL_eq	theorem	theorem _root_.Complexity.NUPPT.distinguisherL_eq (A : NUPPT) (n : ℕ) (w : List Bool) (r : A.Coins n) : A.distinguisherL n w r = decide (A.runAt n w r = [true])
ADDED	TCSlib/Cryptography/Asymptotic/Adversary.lean:82	TCSlib.Cryptography.decodeFin_eq	theorem	theorem decodeFin_eq (ℓ : ℕ) (w : List Bool) : decodeFin ℓ w = if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none
ADDED	TCSlib/Cryptography/Asymptotic/Adversary.lean:183	TCSlib.Cryptography.invProbOpt_def	theorem	theorem invProbOpt_def {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → Option α) : invProbOpt f A = uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1
ADDED	TCSlib/Cryptography/Asymptotic/BlockEncryptor.lean:358	TCSlib.Cryptography.coinBlock_eq	theorem	theorem coinBlock_eq (B i : ℕ) (r : List Bool) : coinBlock B i r = (r.drop (i * B)).take B
ADDED	TCSlib/Cryptography/Asymptotic/BlockEncryptor.lean:276	TCSlib.Cryptography.decListFun_eq	theorem	theorem decListFun_eq (Dc : List Bool → List Bool) (x : List Bool) : decListFun Dc x = (List.range (x.length + 1)).flatMap fun i => decListEmit Dc (decListStep^[i] x)
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:697	TCSlib.Cryptography.Collection.evalSampled_iff	theorem	theorem evalSampled_iff : G.EvalSampled ↔ ∀ n (r : G.gen.Coins n) (s : G.sample.Coins n), ∃ x, G.decD (G.index n r) (G.sample.runAt n (G.index n r) s) = some x ∧ G.eval (pairEncode (G.index n r) (G.sample.runAt n (G.index n r) s)) = G.f (G.index n r) x
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:259	TCSlib.Cryptography.Collection.hardCore_iff	theorem	theorem hardCore_iff (F : Collection) (h : ∀ i, F.D i → Bool) : F.HardCore h ↔ (∃ H : List Bool → List Bool, PolyTimeComputable H ∧ ∀ i x, H (pairEncode i (F.encD i x)) = [h i x]) ∧ ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n, uexp (fun r : F.gen.Coins n => uprob fun z : F.D (F.index n r) × A.Coins n => A.distinguisherL n (pairEncode (F.index n r) (F.f (F.index n r) z.1)) z.2 = h (F.index n r) z.1) ≤ 1 / 2 + ε n
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:185	TCSlib.Cryptography.Collection.index_eq	theorem	theorem index_eq (F : Collection) (n : ℕ) (r : F.gen.Coins n) : F.index n r = pairFstD (F.gen.runAt n [] r)
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:225	TCSlib.Cryptography.Collection.invProbAt_eq	theorem	theorem invProbAt_eq (F : Collection) (A : NUPPT) (n : ℕ) : F.invProbAt A n = uexp fun r : F.gen.Coins n => uprob fun z : F.D (F.index n r) × A.Coins n => ∃ x', F.decD (F.index n r) (A.runAt n (pairEncode (F.index n r) (F.f (F.index n r) z.1)) z.2) = some x' ∧ F.f (F.index n r) x' = F.f (F.index n r) z.1
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:710	TCSlib.Cryptography.Collection.owfCoinsEquiv	def	def owfCoinsEquiv (n : ℕ) : (Fin (G.gen.coins.eval n + G.sample.coins.eval n) → Bool) ≃ (Fin (G.gen.coinLen n + G.sample.coinLen n) → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:716	TCSlib.Cryptography.Collection.owfCoinsEquiv_ofFn	theorem	theorem owfCoinsEquiv_ofFn (n : ℕ) (r : Fin (G.gen.coins.eval n + G.sample.coins.eval n) → Bool) : List.ofFn (G.owfCoinsEquiv n r) = List.ofFn r
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:721	TCSlib.Cryptography.Collection.owfCoinsEquiv_symm_ofFn	theorem	theorem owfCoinsEquiv_symm_ofFn (n : ℕ) (z : Fin (G.gen.coinLen n + G.sample.coinLen n) → Bool) : List.ofFn ((G.owfCoinsEquiv n).symm z) = List.ofFn z
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:206	TCSlib.Cryptography.Collection.sampleClose_iff	theorem	theorem sampleClose_iff (F : Collection) (δ : ℕ → ℝ) : F.SampleClose δ ↔ ∀ n (r : F.gen.Coins n), StatClose (fun s : F.sample.Coins n => F.decD (F.index n r) (F.sample.runAt n (F.index n r) s)) (fun x : F.D (F.index n r) => some x) (δ n)
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:192	TCSlib.Cryptography.Collection.trap_eq	theorem	theorem trap_eq (F : Collection) (n : ℕ) (r : F.gen.Coins n) : F.trap n r = pairSndD (F.gen.runAt n [] r)
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:517	TCSlib.Cryptography.FunFamily.toCollection_decD	theorem	theorem toCollection_decD (i w : List Bool) : (𝓕.toCollection F hF hspec).decD i w = (decodeFin (𝓕.inLen.eval i.length) w).map (𝓕.toCollection_domEquiv F hF hspec i).symm
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:503	TCSlib.Cryptography.FunFamily.toCollection_domEquiv	def	def toCollection_domEquiv (i : List Bool) : (𝓕.toCollection F hF hspec).D i ≃ (Fin (𝓕.inLen.eval i.length) → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:507	TCSlib.Cryptography.FunFamily.toCollection_domEquiv_apply	theorem	theorem toCollection_domEquiv_apply (i : List Bool) (x : (𝓕.toCollection F hF hspec).D i) : 𝓕.toCollection_domEquiv F hF hspec i x = x
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:512	TCSlib.Cryptography.FunFamily.toCollection_encD	theorem	theorem toCollection_encD (i : List Bool) (x : (𝓕.toCollection F hF hspec).D i) : (𝓕.toCollection F hF hspec).encD i x = List.ofFn (𝓕.toCollection_domEquiv F hF hspec i x)
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:538	TCSlib.Cryptography.FunFamily.toCollection_eval	theorem	theorem toCollection_eval (z : List Bool) : (𝓕.toCollection F hF hspec).eval z = F (pairEncode (List.replicate (pairFstD z).length true) (pairSndD z))
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:525	TCSlib.Cryptography.FunFamily.toCollection_f	theorem	theorem toCollection_f (i : List Bool) (x : (𝓕.toCollection F hF hspec).D i) : (𝓕.toCollection F hF hspec).f i x = List.ofFn (𝓕.f i.length (𝓕.toCollection_domEquiv F hF hspec i x))
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:530	TCSlib.Cryptography.FunFamily.toCollection_gen	theorem	theorem toCollection_gen : (𝓕.toCollection F hF hspec).gen = NUPPT.ofPolyTimeUniform (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_const [])) (.const 0)
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:534	TCSlib.Cryptography.FunFamily.toCollection_sample_eq	theorem	theorem toCollection_sample_eq : (𝓕.toCollection F hF hspec).sample = NUPPT.ofPolyTimeUniform NUPPT.polyTimeComputable_inCoins 𝓕.inLen
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:348	TCSlib.Cryptography.PermCollection.oneWay_iff	theorem	theorem PermCollection.oneWay_iff (P : PermCollection) : P.OneWay ↔ P.toCollection.OneWay
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:388	TCSlib.Cryptography.TrapdoorCollection.oneWay_iff	theorem	theorem TrapdoorCollection.oneWay_iff (T : TrapdoorCollection) : T.OneWay ↔ T.toCollection.OneWay
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:395	TCSlib.Cryptography.TrapdoorCollection.toCollection_domEquiv	def	def TrapdoorCollection.toCollection_domEquiv (T : TrapdoorCollection) (i : List Bool) : T.toCollection.D i ≃ T.D i
ADDED	TCSlib/Cryptography/Asymptotic/Collections.lean:399	TCSlib.Cryptography.TrapdoorCollection.toCollection_domEquiv_apply	theorem	theorem TrapdoorCollection.toCollection_domEquiv_apply (T : TrapdoorCollection) (i : List Bool) (x : T.toCollection.D i) : T.toCollection_domEquiv i x = x
ADDED	TCSlib/Cryptography/Asymptotic/CollectionsHelpers.lean:75	Complexity.NUPPT.withIndexParam_coinsEquiv	def	noncomputable def _root_.Complexity.NUPPT.withIndexParam_coinsEquiv (A : NUPPT) (n : ℕ) : A.withIndexParam.Coins n ≃ A.Coins n
ADDED	TCSlib/Cryptography/Asymptotic/CollectionsHelpers.lean:81	Complexity.NUPPT.withIndexParam_coinsEquiv_ofFn	theorem	theorem _root_.Complexity.NUPPT.withIndexParam_coinsEquiv_ofFn (A : NUPPT) (n : ℕ) (r : A.withIndexParam.Coins n) : List.ofFn (A.withIndexParam_coinsEquiv n r) = List.ofFn r
CHANGED	TCSlib/Cryptography/Asymptotic/CollectionsHelpers.lean:72->87	Complexity.NUPPT.withIndexParam_runAt	theorem	theorem _root_.Complexity.NUPPT.withIndexParam_runAt (A : NUPPT) (n : ℕ) (y : List Bool) (r : A.withIndexParam.Coins n) : A.withIndexParam.runAt n y r = A.runAt n (pairEncode (List.replicate n true) y) r	=>	theorem _root_.Complexity.NUPPT.withIndexParam_runAt (A : NUPPT) (n : ℕ) (y : List Bool) (r : A.withIndexParam.Coins n) : A.withIndexParam.runAt n y r = A.runAt n (pairEncode (List.replicate n true) y) (A.withIndexParam_coinsEquiv n r)
ADDED	TCSlib/Cryptography/Asymptotic/CollectionsLemmas.lean:78	TCSlib.Cryptography.padStr_eq	theorem	theorem padStr_eq (p : PolyExpr) (u w : List Bool) : padStr p u w = (w ++ List.replicate (p.eval u.length) false).take (p.eval u.length)
ADDED	TCSlib/Cryptography/Asymptotic/Encryption.lean:229	TCSlib.Cryptography.PrivateKeyScheme.encodeList_nil	theorem	theorem encodeList_nil : encodeList [] = []
ADDED	TCSlib/Cryptography/Asymptotic/Encryption.lean:233	TCSlib.Cryptography.PrivateKeyScheme.multiEncDist_apply	theorem	theorem multiEncDist_apply (S : PrivateKeyScheme) (n q : ℕ) (m : Fin (q + 1) → Fin n → Bool) (r : S.gen.Coins n × (Fin (q + 1) → S.enc.Coins n)) : S.multiEncDist n q m r = encodeList (List.ofFn fun i => S.enc.runAt n (pairEncode (S.gen.runAt n [] r.1) (List.ofFn (m i))) (r.2 i))
ADDED	TCSlib/Cryptography/Asymptotic/Encryption.lean:241	TCSlib.Cryptography.PrivateKeyScheme.multiMessageSecure_iff	theorem	theorem multiMessageSecure_iff (S : PrivateKeyScheme) : S.MultiMessageSecure ↔ ∀ (D : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m m' : Fin (q.eval n + 1) → Fin n → Bool), distAdv (S.multiEncDist n (q.eval n) m) (S.multiEncDist n (q.eval n) m') (D.distinguisherL n) ≤ ε n
ADDED	TCSlib/Cryptography/Asymptotic/Encryption.lean:450	TCSlib.Cryptography.prgScheme_encCoinsEquiv	def	noncomputable def prgScheme_encCoinsEquiv (P : PRG) (F : List Bool → List Bool) (hF : PolyTimeComputable F) (hG : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)) (n : ℕ) : (prgScheme P F hF hG).enc.Coins n ≃ (Fin 0 → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/Encryption.lean:456	TCSlib.Cryptography.prgScheme_encCoinsEquiv_ofFn	theorem	theorem prgScheme_encCoinsEquiv_ofFn (P : PRG) (F : List Bool → List Bool) (hF : PolyTimeComputable F) (hG : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)) (n : ℕ) (r : (prgScheme P F hF hG).enc.Coins n) : List.ofFn (prgScheme_encCoinsEquiv P F hF hG n r) = List.ofFn r
CHANGED	TCSlib/Cryptography/Asymptotic/Encryption.lean:416->464	TCSlib.Cryptography.prgScheme_encDist	theorem	theorem prgScheme_encDist (P : PRG) (F : List Bool → List Bool) (hF : PolyTimeComputable F) (hG : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)) (n : ℕ) (m : Fin n → Bool) (r : (prgScheme P F hF hG).gen.Coins n × (prgScheme P F hF hG).enc.Coins n) : (prgScheme P F hF hG).encDist n m r = List.ofFn (padXor (P.expands n).le m (P.G n r.1))	=>	theorem prgScheme_encDist (P : PRG) (F : List Bool → List Bool) (hF : PolyTimeComputable F) (hG : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)) (n : ℕ) (m : Fin n → Bool) (r : (prgScheme P F hF hG).gen.Coins n × (prgScheme P F hF hG).enc.Coins n) : (prgScheme P F hF hG).encDist n m r = List.ofFn (padXor (P.expands n).le m (P.G n (prgScheme_genCoinsEquiv P F hF hG n r.1)))
ADDED	TCSlib/Cryptography/Asymptotic/Encryption.lean:436	TCSlib.Cryptography.prgScheme_genCoinsEquiv	def	noncomputable def prgScheme_genCoinsEquiv (P : PRG) (F : List Bool → List Bool) (hF : PolyTimeComputable F) (hG : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)) (n : ℕ) : (prgScheme P F hF hG).gen.Coins n ≃ (Fin n → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/Encryption.lean:442	TCSlib.Cryptography.prgScheme_genCoinsEquiv_ofFn	theorem	theorem prgScheme_genCoinsEquiv_ofFn (P : PRG) (F : List Bool → List Bool) (hF : PolyTimeComputable F) (hG : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)) (n : ℕ) (r : (prgScheme P F hF hG).gen.Coins n) : List.ofFn (prgScheme_genCoinsEquiv P F hF hG n r) = List.ofFn r
ADDED	TCSlib/Cryptography/Asymptotic/Ensembles.lean:197	TCSlib.Cryptography.Ensemble.pseudorandom_iff	theorem	theorem pseudorandom_iff (X : Ensemble ℓ) : X.Pseudorandom ↔ Indist X (uniform ℓ)
ADDED	TCSlib/Cryptography/Asymptotic/Ensembles.lean:161	TCSlib.Cryptography.Ensemble.uniform_X	theorem	theorem uniform_X (ℓ : PolyExpr) (n : ℕ) (x : (uniform ℓ).σ n) : (uniform ℓ).X n x = cast (uniform_σ ℓ n) x
ADDED	TCSlib/Cryptography/Asymptotic/Ensembles.lean:157	TCSlib.Cryptography.Ensemble.uniform_σ	theorem	theorem uniform_σ (ℓ : PolyExpr) (n : ℕ) : (uniform ℓ).σ n = (Fin (ℓ.eval n) → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/GGMReduction.lean:144	TCSlib.Cryptography.GGMRed.histEnc_eq	theorem	theorem histEnc_eq {ℓ₁ ℓ₂ : ℕ} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : histEnc h = h.foldr (fun p acc => pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) acc) []
ADDED	TCSlib/Cryptography/Asymptotic/GGMReduction.lean:97	TCSlib.Cryptography.GGMRed.queryOf_eq	theorem	theorem queryOf_eq (ℓ₁ : ℕ) (w : List Bool) : queryOf ℓ₁ w = match pairDecode w with | some ([false], x) => decodeFin ℓ₁ x | _ => none
ADDED	TCSlib/Cryptography/Asymptotic/GGMReduction.lean:107	TCSlib.Cryptography.GGMRed.verdictOf_eq	theorem	theorem verdictOf_eq (w : List Bool) : verdictOf w = decide (w = [true, true])
ADDED	TCSlib/Cryptography/Asymptotic/GGMReductionEval.lean:684	TCSlib.Cryptography.GGMRed.coinPoly_eq	theorem	theorem coinPoly_eq (D : NUPPT) (q : PolyExpr) : coinPoly D q = .add (.mul q .var) (.add (.mul q (.mul (.const 2) .var)) D.coins)
ADDED	TCSlib/Cryptography/Asymptotic/GGMReductionEval.lean:688	TCSlib.Cryptography.GGMRed.coinPoly_eval	theorem	theorem coinPoly_eval (D : NUPPT) (q : PolyExpr) (n : ℕ) : (coinPoly D q).eval n = q.eval n * n + (q.eval n * (2 * n) + D.coinLen n)
ADDED	TCSlib/Cryptography/Asymptotic/GGMReductionEval.lean:249	TCSlib.Cryptography.GGMRed.coinStr_eq	theorem	theorem coinStr_eq : coinStr d = List.ofFn ((FunFamily.blocks (q.eval n) n).symm d.W.1) ++ (List.ofFn ((FunFamily.blocks (q.eval n) (2 * n)).symm fun k => splitHalves.symm (d.W.2 k)) ++ List.ofFn d.r)
ADDED	TCSlib/Cryptography/Asymptotic/GGMReductionEval.lean:727	TCSlib.Cryptography.GGMRed.ggmRedMachine_coinsEquiv	def	noncomputable def ggmRedMachine_coinsEquiv {E : List Bool → List Bool} (hE : PolyTimeComputable E) (D : NUPPT) (q : PolyExpr) (i j : ℕ → ℕ) (n : ℕ) : (ggmRedMachine hE D q i j).Coins n ≃ (Fin (q.eval n * n + (q.eval n * (2 * n) + D.coinLen n)) → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/GGMReductionEval.lean:736	TCSlib.Cryptography.GGMRed.ggmRedMachine_coinsEquiv_ofFn	theorem	theorem ggmRedMachine_coinsEquiv_ofFn {E : List Bool → List Bool} (hE : PolyTimeComputable E) (D : NUPPT) (q : PolyExpr) (i j : ℕ → ℕ) (n : ℕ) (c : (ggmRedMachine hE D q i j).Coins n) : List.ofFn (ggmRedMachine_coinsEquiv hE D q i j n c) = List.ofFn c
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:752	TCSlib.Cryptography.FunFamily.glBit_equiv	theorem	theorem glBit_equiv (n : ℕ) (x r : Fin (𝓕.inLen.eval n) → Bool) : 𝓕.glBit n ((𝓕.glPad_inEquiv n).symm (Fin.append x r)) = HardcoreBit.ip x r
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:746	TCSlib.Cryptography.FunFamily.glPad_f_equiv	theorem	theorem glPad_f_equiv (n : ℕ) (x r : Fin (𝓕.inLen.eval n) → Bool) : 𝓕.glPad_outEquiv n (𝓕.glPad.f n ((𝓕.glPad_inEquiv n).symm (Fin.append x r))) = Fin.append (𝓕.f n x) r
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:703	TCSlib.Cryptography.FunFamily.glPad_inEquiv	def	def glPad_inEquiv (n : ℕ) : (Fin (𝓕.glPad.inLen.eval n) → Bool) ≃ (Fin (𝓕.inLen.eval n + 𝓕.inLen.eval n) → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:714	TCSlib.Cryptography.FunFamily.glPad_inEquiv_ofFn	theorem	theorem glPad_inEquiv_ofFn (n : ℕ) (z : Fin (𝓕.glPad.inLen.eval n) → Bool) : List.ofFn (𝓕.glPad_inEquiv n z) = List.ofFn z
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:718	TCSlib.Cryptography.FunFamily.glPad_inEquiv_symm_ofFn	theorem	theorem glPad_inEquiv_symm_ofFn (n : ℕ) (z : Fin (𝓕.inLen.eval n + 𝓕.inLen.eval n) → Bool) : List.ofFn ((𝓕.glPad_inEquiv n).symm z) = List.ofFn z
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:695	TCSlib.Cryptography.FunFamily.glPad_inLen_eval	theorem	theorem glPad_inLen_eval (n : ℕ) : 𝓕.glPad.inLen.eval n = 𝓕.inLen.eval n + 𝓕.inLen.eval n
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:709	TCSlib.Cryptography.FunFamily.glPad_outEquiv	def	def glPad_outEquiv (n : ℕ) : (Fin (𝓕.glPad.outLen.eval n) → Bool) ≃ (Fin (𝓕.outLen.eval n + 𝓕.inLen.eval n) → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:722	TCSlib.Cryptography.FunFamily.glPad_outEquiv_ofFn	theorem	theorem glPad_outEquiv_ofFn (n : ℕ) (y : Fin (𝓕.glPad.outLen.eval n) → Bool) : List.ofFn (𝓕.glPad_outEquiv n y) = List.ofFn y
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:726	TCSlib.Cryptography.FunFamily.glPad_outEquiv_symm_ofFn	theorem	theorem glPad_outEquiv_symm_ofFn (n : ℕ) (y : Fin (𝓕.outLen.eval n + 𝓕.inLen.eval n) → Bool) : List.ofFn ((𝓕.glPad_outEquiv n).symm y) = List.ofFn y
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:698	TCSlib.Cryptography.FunFamily.glPad_outLen_eval	theorem	theorem glPad_outLen_eval (n : ℕ) : 𝓕.glPad.outLen.eval n = 𝓕.outLen.eval n + 𝓕.inLen.eval n
CHANGED	TCSlib/Cryptography/Asymptotic/HardCore.lean:601->759	TCSlib.Cryptography.FunFamily.predProb_glPad	theorem	theorem predProb_glPad {ρ : Type*} [Fintype ρ] (n : ℕ) (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) : predProb (𝓕.glPad.f n) (𝓕.glBit n) A = predProb (HardcoreBit.glPad (𝓕.f n)) HardcoreBit.glBit (fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r)	=>	theorem predProb_glPad {ρ : Type*} [Fintype ρ] (n : ℕ) (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) : predProb (𝓕.glPad.f n) (𝓕.glBit n) A = predProb (HardcoreBit.glPad (𝓕.f n)) HardcoreBit.glBit (fun y r => A ((𝓕.glPad_outEquiv n).symm (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y)) r)
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:498	TCSlib.Cryptography.PRG.expand_G_stretch	theorem	theorem PRG.expand_G_stretch (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr) (hℓ : ∀ n, n < ℓ.eval n) (n : ℕ) (s : Fin n → Bool) (i : Fin ((PRG.expand G ℓ hℓ).stretch.eval n)) : (PRG.expand G ℓ hℓ).G n s i = G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n)
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:485	TCSlib.Cryptography.PRG.expand_stretch	theorem	theorem PRG.expand_stretch (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr) (hℓ : ∀ n, n < ℓ.eval n) : (PRG.expand G ℓ hℓ).stretch = ℓ
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:298	TCSlib.Cryptography.PRG.oneBit_secure_iff	theorem	theorem PRG.oneBit_secure_iff (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) : (PRG.oneBit G).Secure ↔ (∃ F : List Bool → List Bool, PolyTimeComputable F ∧ ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G n s)) ∧ ∀ D : NUPPT, Negligible fun n => prgAdv (G n) (D.distinguisher n (n + 1))
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:184	TCSlib.Cryptography.PermFamily.HardCore	def	def PermFamily.HardCore (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) : Prop
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:211	TCSlib.Cryptography.PermFamily.HardCore.easy	theorem	theorem PermFamily.HardCore.easy {P : PermFamily} {h : ∀ n, (Fin n → Bool) → Bool} (hh : P.HardCore h) : ∃ H : List Bool → List Bool, PolyTimeComputable H ∧ ∀ n (x : Fin n → Bool), H (NUPPT.advInput n (List.ofFn x)) = [h n x]
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:223	TCSlib.Cryptography.PermFamily.HardCore.hard	theorem	theorem PermFamily.HardCore.hard {P : PermFamily} {h : ∀ n, (Fin n → Bool) → Bool} (hh : P.HardCore h) (A : NUPPT) : ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n, predProb (P.f n) (h n) (A.predictor n n) ≤ 1 / 2 + ε n
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:232	TCSlib.Cryptography.PermFamily.HardCore.of_easy_hard	theorem	theorem PermFamily.HardCore.of_easy_hard {P : PermFamily} {h : ∀ n, (Fin n → Bool) → Bool} (he : ∃ H : List Bool → List Bool, PolyTimeComputable H ∧ ∀ n (x : Fin n → Bool), H (NUPPT.advInput n (List.ofFn x)) = [h n x]) (hA : ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n, predProb (P.f n) (h n) (A.predictor n n) ≤ 1 / 2 + ε n) : P.HardCore h
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:189	TCSlib.Cryptography.PermFamily.hardCore_iff	theorem	theorem PermFamily.hardCore_iff (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) : P.HardCore h ↔ TCSlib.Cryptography.HardCore P.toFunFamily fun n x => h n (P.toFunFamily_domEquiv n x)
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:197	TCSlib.Cryptography.PermFamily.predProb_toFunFamily	theorem	theorem PermFamily.predProb_toFunFamily (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (A : NUPPT) (n : ℕ) : predProb (P.toFunFamily.f n) (fun x => h n (P.toFunFamily_domEquiv n x)) (A.predictor n (P.toFunFamily.outLen.eval n)) = predProb (P.f n) (h n) (A.predictor n n)
CHANGED	TCSlib/Cryptography/Asymptotic/HardCore.lean:549->660	TCSlib.Cryptography.cor_81_7	theorem	theorem cor_81_7 (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (ℓ : PolyExpr) (hℓ : ∀ n, n ≤ ℓ.eval n) (hP : OneWayPermutation P) (hh : HardCore P.toFunFamily h) : (P.iterPRG h ℓ hℓ).Secure	=>	theorem cor_81_7 (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (ℓ : PolyExpr) (hℓ : ∀ n, n ≤ ℓ.eval n) (hP : OneWayPermutation P) (hh : P.HardCore h) : (P.iterPRG h ℓ hℓ).Secure
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:318	TCSlib.Cryptography.owpGenPRG_G_outEquiv	theorem	theorem owpGenPRG_G_outEquiv (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) (s : Fin n → Bool) : owpGenPRG_outEquiv P h n ((owpGenPRG P h).G n s) = Fin.snoc (P.f n s) (h n s)
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:313	TCSlib.Cryptography.owpGenPRG_outEquiv	def	def owpGenPRG_outEquiv (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) : (Fin ((owpGenPRG P h).stretch.eval n) → Bool) ≃ (Fin (n + 1) → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/HardCore.lean:324	TCSlib.Cryptography.owpGenPRG_outEquiv_ofFn	theorem	theorem owpGenPRG_outEquiv_ofFn (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) (y : Fin ((owpGenPRG P h).stretch.eval n) → Bool) : List.ofFn (owpGenPRG_outEquiv P h n y) = List.ofFn y
CHANGED	TCSlib/Cryptography/Asymptotic/HardCore.lean:329->424	TCSlib.Cryptography.owp_hardcore_prg	theorem	theorem owp_hardcore_prg (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (hP : OneWayPermutation P) (hh : HardCore P.toFunFamily h) : (owpGenPRG P h).Secure	=>	theorem owp_hardcore_prg (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (hP : OneWayPermutation P) (hh : P.HardCore h) : (owpGenPRG P h).Secure
CHANGED	TCSlib/Cryptography/Asymptotic/HardCoreClaims.lean:75->75	TCSlib.Cryptography.thm_87_3_1	theorem	theorem thm_87_3_1 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] (n : ℕ) (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) (h : predProb (𝓕.glPad.f n) (𝓕.glBit n) A = 1) : invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.perfectRecover fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r)) = 1	=>	theorem thm_87_3_1 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] (n : ℕ) (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) (h : predProb (𝓕.glPad.f n) (𝓕.glBit n) A = 1) : invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.perfectRecover fun y r => A ((𝓕.glPad_outEquiv n).symm (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y)) r)) = 1
CHANGED	TCSlib/Cryptography/Asymptotic/HardCoreClaims.lean:88->90	TCSlib.Cryptography.thm_87_3_2	theorem	theorem thm_87_3_2 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] [Nonempty ρ] (n : ℕ) (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) {T : ℕ} {ε : ℝ} (hε : 0 < ε) (hT : (𝓕.inLen.eval n : ℝ) ≤ 2 * ε ^ 2 * T) (h : 3 / 4 + ε ≤ predProb (𝓕.glPad.f n) (𝓕.glBit n) A) : ε / 4 ≤ invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.majorityRecover (fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r) T))	=>	theorem thm_87_3_2 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] [Nonempty ρ] (n : ℕ) (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) {T : ℕ} {ε : ℝ} (hε : 0 < ε) (hT : (𝓕.inLen.eval n : ℝ) ≤ 2 * ε ^ 2 * T) (h : 3 / 4 + ε ≤ predProb (𝓕.glPad.f n) (𝓕.glBit n) A) : ε / 4 ≤ invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.majorityRecover (fun y r => A ((𝓕.glPad_outEquiv n).symm (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y)) r) T))
CHANGED	TCSlib/Cryptography/Asymptotic/HardCoreClaims.lean:101->105	TCSlib.Cryptography.thm_87_3_3	theorem	theorem thm_87_3_3 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] (n : ℕ) (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε) (h : c + ε ≤ predProb (𝓕.glPad.f n) (𝓕.glBit n) A) : ε / 2 ≤ uprob fun x => c + ε / 2 ≤ HardcoreBit.secProb (𝓕.f n) (fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r) x	=>	theorem thm_87_3_3 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] (n : ℕ) (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε) (h : c + ε ≤ predProb (𝓕.glPad.f n) (𝓕.glBit n) A) : ε / 2 ≤ uprob fun x => c + ε / 2 ≤ HardcoreBit.secProb (𝓕.f n) (fun y r => A ((𝓕.glPad_outEquiv n).symm (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y)) r) x
CHANGED	TCSlib/Cryptography/Asymptotic/HardCoreClaims.lean:155->160	TCSlib.Cryptography.thm_87_3_9	theorem	theorem thm_87_3_9 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] [Nonempty ρ] (n : ℕ) (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) {k : ℕ} {ε : ℝ} (hε : 0 < ε) (hk : 2 * (𝓕.inLen.eval n : ℝ) ≤ ε ^ 2 * ((2 : ℝ) ^ k - 1)) (h : 1 / 2 + ε ≤ predProb (𝓕.glPad.f n) (𝓕.glBit n) A) : ε / (4 * 2 ^ k) ≤ invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.guessRecover (fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r) k)) ∧ (ε ^ 2 * (2 : ℝ) ^ k ≤ 4 * 𝓕.inLen.eval n → ε ^ 3 / (16 * 𝓕.inLen.eval n) ≤ invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.guessRecover (fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r) k)))	=>	theorem thm_87_3_9 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] [Nonempty ρ] (n : ℕ) (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) {k : ℕ} {ε : ℝ} (hε : 0 < ε) (hk : 2 * (𝓕.inLen.eval n : ℝ) ≤ ε ^ 2 * ((2 : ℝ) ^ k - 1)) (h : 1 / 2 + ε ≤ predProb (𝓕.glPad.f n) (𝓕.glBit n) A) : ε / (4 * 2 ^ k) ≤ invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.guessRecover (fun y r => A ((𝓕.glPad_outEquiv n).symm (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y)) r) k)) ∧ (ε ^ 2 * (2 : ℝ) ^ k ≤ 4 * 𝓕.inLen.eval n → ε ^ 3 / (16 * 𝓕.inLen.eval n) ≤ invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.guessRecover (fun y r => A ((𝓕.glPad_outEquiv n).symm (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y)) r) k)))
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:226	TCSlib.Cryptography.Collection.glPad_decD	theorem	theorem glPad_decD (m : PolyExpr) (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) (i w : List Bool) : (F.glPad m henc).decD i w = (glPadDecode F i (F.encD i default).length w).map (glPad_domEquiv m henc i).symm
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:201	TCSlib.Cryptography.Collection.glPad_domEquiv	def	def glPad_domEquiv (m : PolyExpr) (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) (i : List Bool) : (F.glPad m henc).D i ≃ F.D i × (Fin (F.encD i default).length → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:209	TCSlib.Cryptography.Collection.glPad_domEquiv_apply	theorem	theorem glPad_domEquiv_apply (m : PolyExpr) (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) (i : List Bool) (z : (F.glPad m henc).D i) : glPad_domEquiv m henc i z = z
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:216	TCSlib.Cryptography.Collection.glPad_encD	theorem	theorem glPad_encD (m : PolyExpr) (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) (i : List Bool) (z : (F.glPad m henc).D i) : (F.glPad m henc).encD i z = pairEncode (F.encD i (glPad_domEquiv m henc i z).1) (List.ofFn (glPad_domEquiv m henc i z).2)
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:254	TCSlib.Cryptography.Collection.glPad_eval	theorem	theorem glPad_eval (m : PolyExpr) (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) (w : List Bool) : (F.glPad m henc).eval w = pairEncode (F.eval (pairEncode (pairFstD w) (pairFstD (pairSndD w)))) (pairSndD (pairSndD w))
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:237	TCSlib.Cryptography.Collection.glPad_f_domEquiv	theorem	theorem glPad_f_domEquiv (m : PolyExpr) (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) (i : List Bool) (z : (F.glPad m henc).D i) : (F.glPad m henc).f i z = pairEncode (F.f i (glPad_domEquiv m henc i z).1) (List.ofFn (glPad_domEquiv m henc i z).2)
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:263	TCSlib.Cryptography.Collection.glPad_index	theorem	theorem glPad_index (m : PolyExpr) (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) (n : ℕ) (r : F.gen.Coins n) : (F.glPad m henc).index n r = F.index n r
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:272	TCSlib.Cryptography.Collection.glPad_invProbAt	theorem	theorem glPad_invProbAt (m : PolyExpr) (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) (A : NUPPT) (n : ℕ) : (F.glPad m henc).invProbAt A n = uexp fun r : F.gen.Coins n => uprob fun z : (F.D (F.index n r) × (Fin (F.encD (F.index n r) default).length → Bool)) × A.Coins n => ∃ x', glPadDecode F (F.index n r) (F.encD (F.index n r) default).length (A.runAt n (pairEncode (F.index n r) (pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2))) z.2) = some x' ∧ pairEncode (F.f (F.index n r) x'.1) (List.ofFn x'.2) = pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2)
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:247	TCSlib.Cryptography.Collection.glPad_sample	theorem	theorem glPad_sample (m : PolyExpr) (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) : (F.glPad m henc).sample = NUPPT.ofPolyTimeUniform (glPadSampleFun_poly F) (.add F.sample.coins m)
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:394	TCSlib.Cryptography.PermCollection.glPad_domEquiv	def	def PermCollection.glPad_domEquiv (P : PermCollection) (m : PolyExpr) (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n) (i : List Bool) : (P.glPad m henc).D i ≃ P.D i × (Fin (P.encD i default).length → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:401	TCSlib.Cryptography.PermCollection.glPad_domEquiv_apply	theorem	theorem PermCollection.glPad_domEquiv_apply (P : PermCollection) (m : PolyExpr) (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n) (i : List Bool) (z : (P.glPad m henc).D i) : P.glPad_domEquiv m henc i z = z
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:407	TCSlib.Cryptography.PermCollection.glPad_perm	theorem	theorem PermCollection.glPad_perm (P : PermCollection) (m : PolyExpr) (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n) (i : List Bool) : (P.glPad m henc).perm i = ((P.glPad_domEquiv m henc i).trans ((P.perm i).prodCongr (Equiv.refl _))).trans (P.glPad_domEquiv m henc i).symm
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:498	TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_hardCore_domEquiv	theorem	theorem TrapdoorCollection.OneWay.glPad_hardCore_domEquiv {T : TrapdoorCollection} (m : PolyExpr) (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) (h : T.OneWay) : (T.glPad m henc).toCollection.HardCore fun i z => T.glBit i (T.glPad_domEquiv m henc i z)
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:461	TCSlib.Cryptography.TrapdoorCollection.glPad_domEquiv	def	def TrapdoorCollection.glPad_domEquiv (T : TrapdoorCollection) (m : PolyExpr) (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) (i : List Bool) : (T.glPad m henc).D i ≃ T.D i × (Fin (T.encD i default).length → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:468	TCSlib.Cryptography.TrapdoorCollection.glPad_domEquiv_apply	theorem	theorem TrapdoorCollection.glPad_domEquiv_apply (T : TrapdoorCollection) (m : PolyExpr) (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) (i : List Bool) (z : (T.glPad m henc).D i) : T.glPad_domEquiv m henc i z = z
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:474	TCSlib.Cryptography.TrapdoorCollection.glPad_inv	theorem	theorem TrapdoorCollection.glPad_inv (T : TrapdoorCollection) (m : PolyExpr) (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) : (T.glPad m henc).inv = NUPPT.ofPolyTimeUniform (glPadInvFun_poly T) T.inv.coins
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreGL.lean:519	Complexity.NUPPT.precomp_coinsEquiv	def	noncomputable def precomp_coinsEquiv (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre) (n : ℕ) : (A.precomp hpre).Coins n ≃ A.Coins n
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreGL.lean:525	Complexity.NUPPT.precomp_coinsEquiv_ofFn	theorem	theorem precomp_coinsEquiv_ofFn (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre) (n : ℕ) (c : (A.precomp hpre).Coins n) : List.ofFn (A.precomp_coinsEquiv hpre n c) = List.ofFn c
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreGL.lean:692	TCSlib.Cryptography.glMachine_coinsEquiv	def	noncomputable def glMachine_coinsEquiv (A : NUPPT) (mP K : PolyExpr) (k : ℕ → ℕ) (hk : ∀ n, 2 ^ k n ≤ K.eval n) (n : ℕ) : (glMachine A mP K k hk).Coins n ≃ (Fin ((glCoins mP K A).eval n) → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreGL.lean:699	TCSlib.Cryptography.glMachine_coinsEquiv_symm_ofFn	theorem	theorem glMachine_coinsEquiv_symm_ofFn (A : NUPPT) (mP K : PolyExpr) (k : ℕ → ℕ) (hk : ∀ n, 2 ^ k n ≤ K.eval n) (n : ℕ) (w : Fin ((glCoins mP K A).eval n) → Bool) : List.ofFn ((glMachine_coinsEquiv A mP K k hk n).symm w) = List.ofFn w
CHANGED	TCSlib/Cryptography/Asymptotic/HardCoreGL.lean:833->872	TCSlib.Cryptography.glMachine_runAt_guessRecover	theorem	theorem glMachine_runAt_guessRecover (A₁ : NUPPT) (iP K : PolyExpr) (k : ℕ → ℕ) (hk : ∀ n, 2 ^ k n ≤ K.eval n) (n : ℕ) (hM : 0 < 2 ^ k n - 1 ∨ iP.eval n = 0) {β : Type*} (enc : β → List Bool) (y : β) (g : HardcoreBit.GuessCoins (iP.eval n) (k n) (A₁.Coins n)) (ex : Fin ((glCoins iP K A₁).eval n - glNeed A₁ iP k n) → Bool) : (glMachine A₁ iP K k hk).runAt n (enc y) (glCoinsEquiv A₁ n (iP.eval n) (k n) _ (glNeed_le A₁ iP K k hk n) (g, ex)) = List.ofFn (HardcoreBit.guessRecover (glPredictorOf A₁ n (iP.eval n) enc) (k n) y g)	=>	theorem glMachine_runAt_guessRecover (A₁ : NUPPT) (iP K : PolyExpr) (k : ℕ → ℕ) (hk : ∀ n, 2 ^ k n ≤ K.eval n) (n : ℕ) (hM : 0 < 2 ^ k n - 1 ∨ iP.eval n = 0) {β : Type*} (enc : β → List Bool) (y : β) (g : HardcoreBit.GuessCoins (iP.eval n) (k n) (A₁.Coins n)) (ex : Fin ((glCoins iP K A₁).eval n - glNeed A₁ iP k n) → Bool) : (glMachine A₁ iP K k hk).runAt n (enc y) ((glMachine_coinsEquiv A₁ iP K k hk n).symm (glCoinsEquiv A₁ n (iP.eval n) (k n) _ (glNeed_le A₁ iP K k hk n) (g, ex))) = List.ofFn (HardcoreBit.guessRecover (glPredictorOf A₁ n (iP.eval n) enc) (k n) y g)
CHANGED	TCSlib/Cryptography/Asymptotic/HardCoreGL.lean:673->707	TCSlib.Cryptography.glNeed	abbrev	def glNeed (A : NUPPT) (mP : PolyExpr) (k : ℕ → ℕ) (n : ℕ) : ℕ	=>	abbrev glNeed (A : NUPPT) (mP : PolyExpr) (k : ℕ → ℕ) (n : ℕ) : ℕ
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreGL.lean:860	TCSlib.Cryptography.glPredictorOf_apply	theorem	theorem glPredictorOf_apply (A₁ : NUPPT) (n m : ℕ) {β : Type*} (enc : β → List Bool) (p : β × (Fin m → Bool)) (c : A₁.Coins n) : glPredictorOf A₁ n m enc p c = decide (A₁.runAtL n (pairEncode (enc p.1) (List.ofFn p.2)) (List.ofFn c) = [true])
CHANGED	TCSlib/Cryptography/Asymptotic/HardCoreGLColl.lean:171->171	TCSlib.Cryptography.glPredictorOf_precomp_coll	theorem	theorem glPredictorOf_precomp_coll (A : NUPPT) (n m : ℕ) (i y : List Bool) (q : Fin m → Bool) (c : A.Coins n) : glPredictorOf (A.precomp collPre_poly) n m (fun y : List Bool => pairEncode i y) (y, q) c = A.distinguisherL n (pairEncode i (pairEncode y (List.ofFn q))) c	=>	theorem glPredictorOf_precomp_coll (A : NUPPT) (n m : ℕ) (i y : List Bool) (q : Fin m → Bool) (c : (A.precomp collPre_poly).Coins n) : glPredictorOf (A.precomp collPre_poly) n m (fun y : List Bool => pairEncode i y) (y, q) c = A.distinguisherL n (pairEncode i (pairEncode y (List.ofFn q))) (A.precomp_coinsEquiv collPre_poly n c)
CHANGED	TCSlib/Cryptography/Asymptotic/HardCoreGLFamily.lean:169->169	TCSlib.Cryptography.glPredictorOf_precomp_concat	theorem	theorem glPredictorOf_precomp_concat (A : NUPPT) (n o m : ℕ) (y : Fin o → Bool) (q : Fin m → Bool) (c : A.Coins n) : glPredictorOf (A.precomp concatPre_poly) n m (fun y : Fin o → Bool => List.ofFn y) (y, q) c = A.predictor n (o + m) (Fin.appendEquiv o m (y, q)) c	=>	theorem glPredictorOf_precomp_concat (A : NUPPT) (n o m : ℕ) (y : Fin o → Bool) (q : Fin m → Bool) (c : (A.precomp concatPre_poly).Coins n) : glPredictorOf (A.precomp concatPre_poly) n m (fun y : Fin o → Bool => List.ofFn y) (y, q) c = A.predictor n (o + m) (Fin.appendEquiv o m (y, q)) (A.precomp_coinsEquiv concatPre_poly n c)
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean:173	Complexity.NUPPT.wrapCoinsEquiv	def	noncomputable def wrapCoinsEquiv (A : NUPPT) {pre post : List Bool → List Bool} (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool) (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) (n : ℕ) : (A.wrap hpre hpost β b hβ p).Coins n ≃ (Fin (p.eval n + A.coinLen n) → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean:182	Complexity.NUPPT.wrapCoinsEquiv_symm_ofFn	theorem	theorem wrapCoinsEquiv_symm_ofFn (A : NUPPT) {pre post : List Bool → List Bool} (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool) (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) (n : ℕ) (w : Fin (p.eval n + A.coinLen n) → Bool) : List.ofFn ((A.wrapCoinsEquiv hpre hpost β b hβ p n).symm w) = List.ofFn w
ADDED	TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean:983	TCSlib.Cryptography.glPadInvFun_eq	theorem	theorem glPadInvFun_eq (T : TrapdoorCollection) (z : List Bool) : glPadInvFun T z = pairEncode (T.inv.output (NUPPT.layout (NUPPT.inParam z) (pairEncode (pairFstD (NUPPT.inArg z)) (pairFstD (pairSndD (NUPPT.inArg z)))) [] (NUPPT.inCoins z))) (pairSndD (pairSndD (NUPPT.inArg z)))
ADDED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:242	TCSlib.Cryptography.HardcoreBit.ip_eq_of_ofFn	theorem	theorem HardcoreBit.ip_eq_of_ofFn {k m : ℕ} (h : k = m) {x' r' : Fin k → Bool} {x r : Fin m → Bool} (hx : List.ofFn x' = List.ofFn x) (hr : List.ofFn r' = List.ofFn r) : HardcoreBit.ip x' r' = HardcoreBit.ip x r
CHANGED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:631->794	TCSlib.Cryptography.OneWayPermutation.glHalf	theorem	theorem OneWayPermutation.glHalf {P : PermFamily} (hP : OneWayPermutation P) : OneWayPermutation P.glHalf ∧ HardCore P.glHalf.toFunFamily glHalfBit	=>	theorem OneWayPermutation.glHalf {P : PermFamily} (hP : OneWayPermutation P) : OneWayPermutation P.glHalf ∧ P.glHalf.HardCore glHalfBit
ADDED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:250	TCSlib.Cryptography.PermFamily.glBit_append	theorem	theorem PermFamily.glBit_append (P : PermFamily) (m : ℕ) (x r : Fin m → Bool) : P.toFunFamily.glBit m ((P.glPad_inEquiv m).symm (Fin.append x r)) = HardcoreBit.ip x r
CHANGED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:177->262	TCSlib.Cryptography.PermFamily.glHalf_f_even	theorem	theorem PermFamily.glHalf_f_even (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) : P.glHalf.f (m + m) z = P.toFunFamily.glPad.f m z	=>	theorem PermFamily.glHalf_f_even (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) : P.glHalf.f (m + m) z = P.glPad_outEquiv m (P.toFunFamily.glPad.f m ((P.glPad_inEquiv m).symm z))
CHANGED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:241->337	TCSlib.Cryptography.PermFamily.glHalf_f_odd	theorem	theorem PermFamily.glHalf_f_odd (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) (e : Bool) : P.glHalf.f (m + m + 1) (Fin.snoc z e) = Fin.snoc (P.toFunFamily.glPad.f m z) e	=>	theorem PermFamily.glHalf_f_odd (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) (e : Bool) : P.glHalf.f (m + m + 1) (Fin.snoc z e) = Fin.snoc (P.glPad_outEquiv m (P.toFunFamily.glPad.f m ((P.glPad_inEquiv m).symm z))) e
ADDED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:230	TCSlib.Cryptography.PermFamily.glPad_f_append	theorem	theorem PermFamily.glPad_f_append (P : PermFamily) (m : ℕ) (x r : Fin m → Bool) : P.glPad_outEquiv m (P.toFunFamily.glPad.f m ((P.glPad_inEquiv m).symm (Fin.append x r))) = Fin.append (P.f m x) r
ADDED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:186	TCSlib.Cryptography.PermFamily.glPad_inEquiv	def	def PermFamily.glPad_inEquiv (P : PermFamily) (m : ℕ) : (Fin (P.toFunFamily.glPad.inLen.eval m) → Bool) ≃ (Fin (m + m) → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:198	TCSlib.Cryptography.PermFamily.glPad_inEquiv_ofFn	theorem	theorem PermFamily.glPad_inEquiv_ofFn (P : PermFamily) (m : ℕ) (z : Fin (P.toFunFamily.glPad.inLen.eval m) → Bool) : List.ofFn (P.glPad_inEquiv m z) = List.ofFn z
ADDED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:221	TCSlib.Cryptography.PermFamily.glPad_inEquiv_symm_append	theorem	theorem PermFamily.glPad_inEquiv_symm_append (P : PermFamily) (m : ℕ) (x r : Fin m → Bool) : (P.glPad_inEquiv m).symm (Fin.append x r) = (P.toFunFamily.glPad_inEquiv m).symm (Fin.append ((P.toFunFamily_domEquiv m).symm x) ((P.toFunFamily_domEquiv m).symm r))
ADDED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:204	TCSlib.Cryptography.PermFamily.glPad_inEquiv_symm_ofFn	theorem	theorem PermFamily.glPad_inEquiv_symm_ofFn (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) : List.ofFn ((P.glPad_inEquiv m).symm z) = List.ofFn z
ADDED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:174	TCSlib.Cryptography.PermFamily.glPad_inLen_eval	theorem	theorem PermFamily.glPad_inLen_eval (P : PermFamily) (m : ℕ) : P.toFunFamily.glPad.inLen.eval m = m + m
ADDED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:193	TCSlib.Cryptography.PermFamily.glPad_outEquiv	def	def PermFamily.glPad_outEquiv (P : PermFamily) (m : ℕ) : (Fin (P.toFunFamily.glPad.outLen.eval m) → Bool) ≃ (Fin (m + m) → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:209	TCSlib.Cryptography.PermFamily.glPad_outEquiv_ofFn	theorem	theorem PermFamily.glPad_outEquiv_ofFn (P : PermFamily) (m : ℕ) (y : Fin (P.toFunFamily.glPad.outLen.eval m) → Bool) : List.ofFn (P.glPad_outEquiv m y) = List.ofFn y
ADDED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:215	TCSlib.Cryptography.PermFamily.glPad_outEquiv_symm_ofFn	theorem	theorem PermFamily.glPad_outEquiv_symm_ofFn (P : PermFamily) (m : ℕ) (y : Fin (m + m) → Bool) : List.ofFn ((P.glPad_outEquiv m).symm y) = List.ofFn y
ADDED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:179	TCSlib.Cryptography.PermFamily.glPad_outLen_eval	theorem	theorem PermFamily.glPad_outLen_eval (P : PermFamily) (m : ℕ) : P.toFunFamily.glPad.outLen.eval m = m + m
CHANGED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:676->841	TCSlib.Cryptography.exists_owp_hardCore	theorem	theorem exists_owp_hardCore (h : ∃ P : PermFamily, OneWayPermutation P) : ∃ (P : PermFamily) (b : ∀ n, (Fin n → Bool) → Bool), OneWayPermutation P ∧ HardCore P.toFunFamily b	=>	theorem exists_owp_hardCore (h : ∃ P : PermFamily, OneWayPermutation P) : ∃ (P : PermFamily) (b : ∀ n, (Fin n → Bool) → Bool), OneWayPermutation P ∧ P.HardCore b
CHANGED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:197->286	TCSlib.Cryptography.glHalfBit_even	theorem	theorem glHalfBit_even (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) : glHalfBit (m + m) z = P.toFunFamily.glBit m z	=>	theorem glHalfBit_even (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) : glHalfBit (m + m) z = P.toFunFamily.glBit m ((P.glPad_inEquiv m).symm z)
CHANGED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:274->374	TCSlib.Cryptography.glHalfBit_odd	theorem	theorem glHalfBit_odd (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) (e : Bool) : glHalfBit (m + m + 1) (Fin.snoc z e) = P.toFunFamily.glBit m z	=>	theorem glHalfBit_odd (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) (e : Bool) : glHalfBit (m + m + 1) (Fin.snoc z e) = P.toFunFamily.glBit m ((P.glPad_inEquiv m).symm z)
CHANGED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:552->714	TCSlib.Cryptography.glHalf_predProb_even	theorem	theorem glHalf_predProb_even (P : PermFamily) (A : NUPPT) (m : ℕ) : predProb (P.glHalf.f (m + m)) (glHalfBit (m + m)) (A.predictor (m + m) (m + m)) = predProb (P.toFunFamily.glPad.f m) (P.toFunFamily.glBit m) ((A.reparam (.add .var .var)).predictor m (m + m))	=>	theorem glHalf_predProb_even (P : PermFamily) (A : NUPPT) (m : ℕ) : predProb (P.glHalf.f (m + m)) (glHalfBit (m + m)) (A.predictor (m + m) (m + m)) = predProb (P.toFunFamily.glPad.f m) (P.toFunFamily.glBit m) ((A.reparam (.add .var .var)).predictor m (P.toFunFamily.glPad.outLen.eval m))
CHANGED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:563->726	TCSlib.Cryptography.glHalf_predProb_odd	theorem	theorem glHalf_predProb_odd (P : PermFamily) (A : NUPPT) (m : ℕ) : predProb (P.glHalf.f (m + m + 1)) (glHalfBit (m + m + 1)) (A.predictor (m + m + 1) (m + m + 1)) = predProb (P.toFunFamily.glPad.f m) (P.toFunFamily.glBit m) ((glHalfOddPred A).predictor m (m + m))	=>	theorem glHalf_predProb_odd (P : PermFamily) (A : NUPPT) (m : ℕ) : predProb (P.glHalf.f (m + m + 1)) (glHalfBit (m + m + 1)) (A.predictor (m + m + 1) (m + m + 1)) = predProb (P.toFunFamily.glPad.f m) (P.toFunFamily.glBit m) ((glHalfOddPred A).predictor m (P.toFunFamily.glPad.outLen.eval m))
CHANGED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:222->315	TCSlib.Cryptography.invProb_glHalf_even	theorem	theorem invProb_glHalf_even {ρ : Type*} [Fintype ρ] (P : PermFamily) (m : ℕ) (A : (Fin (m + m) → Bool) → ρ → (Fin (m + m) → Bool)) : invProb (P.glHalf.f (m + m)) A = invProb (P.toFunFamily.glPad.f m) A	=>	theorem invProb_glHalf_even {ρ : Type*} [Fintype ρ] (P : PermFamily) (m : ℕ) (A : (Fin (m + m) → Bool) → ρ → (Fin (m + m) → Bool)) : invProb (P.glHalf.f (m + m)) A = invProb (P.toFunFamily.glPad.f m) (fun y r => (P.glPad_inEquiv m).symm (A (P.glPad_outEquiv m y) r))
CHANGED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:323->434	TCSlib.Cryptography.invProb_glHalf_odd_le	theorem	theorem invProb_glHalf_odd_le {ρ : Type*} [Fintype ρ] (P : PermFamily) (m : ℕ) (A : (Fin (m + m + 1) → Bool) → ρ → (Fin (m + m + 1) → Bool)) : invProb (P.glHalf.f (m + m + 1)) A ≤ invProb (P.toFunFamily.glPad.f m) (fun (y : Fin (m + m) → Bool) (c : Bool × ρ) => Fin.init (A (Fin.snoc y c.1) c.2))	=>	theorem invProb_glHalf_odd_le {ρ : Type*} [Fintype ρ] (P : PermFamily) (m : ℕ) (A : (Fin (m + m + 1) → Bool) → ρ → (Fin (m + m + 1) → Bool)) : invProb (P.glHalf.f (m + m + 1)) A ≤ invProb (P.toFunFamily.glPad.f m) (fun y (c : Bool × ρ) => (P.glPad_inEquiv m).symm (Fin.init (A (Fin.snoc (P.glPad_outEquiv m y) c.1) c.2)))
CHANGED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:211->302	TCSlib.Cryptography.predProb_glHalf_even	theorem	theorem predProb_glHalf_even {ρ : Type*} [Fintype ρ] (P : PermFamily) (m : ℕ) (A : (Fin (m + m) → Bool) → ρ → Bool) : predProb (P.glHalf.f (m + m)) (glHalfBit (m + m)) A = predProb (P.toFunFamily.glPad.f m) (P.toFunFamily.glBit m) A	=>	theorem predProb_glHalf_even {ρ : Type*} [Fintype ρ] (P : PermFamily) (m : ℕ) (A : (Fin (m + m) → Bool) → ρ → Bool) : predProb (P.glHalf.f (m + m)) (glHalfBit (m + m)) A = predProb (P.toFunFamily.glPad.f m) (P.toFunFamily.glBit m) (fun y r => A (P.glPad_outEquiv m y) r)
CHANGED	TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean:307->409	TCSlib.Cryptography.predProb_glHalf_odd	theorem	theorem predProb_glHalf_odd {ρ : Type*} [Fintype ρ] (P : PermFamily) (m : ℕ) (A : (Fin (m + m + 1) → Bool) → ρ → Bool) : predProb (P.glHalf.f (m + m + 1)) (glHalfBit (m + m + 1)) A = predProb (P.toFunFamily.glPad.f m) (P.toFunFamily.glBit m) (fun (y : Fin (m + m) → Bool) (c : Bool × ρ) => A (Fin.snoc y c.1) c.2)	=>	theorem predProb_glHalf_odd {ρ : Type*} [Fintype ρ] (P : PermFamily) (m : ℕ) (A : (Fin (m + m + 1) → Bool) → ρ → Bool) : predProb (P.glHalf.f (m + m + 1)) (glHalfBit (m + m + 1)) A = predProb (P.toFunFamily.glPad.f m) (P.toFunFamily.glBit m) (fun y (c : Bool × ρ) => A (Fin.snoc (P.glPad_outEquiv m y) c.1) c.2)
ADDED	TCSlib/Cryptography/Asymptotic/OneWay.lean:247	TCSlib.Cryptography.FunFamily.blocks_apply	theorem	theorem blocks_apply (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) : blocks q ℓ x i j = x (finProdFinEquiv (i, j))
ADDED	TCSlib/Cryptography/Asymptotic/OneWay.lean:115	TCSlib.Cryptography.FunFamily.easy_iff	theorem	theorem easy_iff (𝓕 : FunFamily) : 𝓕.Easy ↔ ∃ F : List Bool → List Bool, PolyTimeComputable F ∧ ∀ n (x : Fin (𝓕.inLen.eval n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)
ADDED	TCSlib/Cryptography/Asymptotic/OneWay.lean:376	TCSlib.Cryptography.FunFamily.ofFn_ofString_apply	theorem	theorem ofFn_ofString_apply {f : List Bool → List Bool} {p : PolyExpr} (hf : LengthRegular f p) (n : ℕ) (x : Fin ((ofString f p).inLen.eval n) → Bool) : List.ofFn ((ofString f p).f n x) = f (List.ofFn x)
ADDED	TCSlib/Cryptography/Asymptotic/OneWay.lean:232	TCSlib.Cryptography.FunFamily.ofString_f_apply	theorem	theorem ofString_f_apply (f : List Bool → List Bool) (p : PolyExpr) (n : ℕ) (x : Fin ((ofString f p).inLen.eval n) → Bool) (i : Fin ((ofString f p).outLen.eval n)) : (ofString f p).f n x i = (f (List.ofFn x)).getD i false
ADDED	TCSlib/Cryptography/Asymptotic/OneWay.lean:226	TCSlib.Cryptography.FunFamily.ofString_inLen_eval	theorem	theorem ofString_inLen_eval (f p) (n : ℕ) : (ofString f p).inLen.eval n = n
ADDED	TCSlib/Cryptography/Asymptotic/OneWay.lean:229	TCSlib.Cryptography.FunFamily.ofString_outLen_eval	theorem	theorem ofString_outLen_eval (f p) (n : ℕ) : (ofString f p).outLen.eval n = p.eval n
ADDED	TCSlib/Cryptography/Asymptotic/OneWay.lean:955	TCSlib.Cryptography.OneWayPermutation.evaluator	theorem	theorem OneWayPermutation.evaluator {P : PermFamily} (hP : OneWayPermutation P) : ∃ F : List Bool → List Bool, PolyTimeComputable F ∧ ∀ n (x : Fin n → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (P.f n x)
ADDED	TCSlib/Cryptography/Asymptotic/OneWay.lean:977	TCSlib.Cryptography.PermFamily.toFunFamily_codEquiv	def	def PermFamily.toFunFamily_codEquiv (P : PermFamily) (n : ℕ) : (Fin (P.toFunFamily.outLen.eval n) → Bool) ≃ (Fin n → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/OneWay.lean:990	TCSlib.Cryptography.PermFamily.toFunFamily_codEquiv_ofFn	theorem	theorem PermFamily.toFunFamily_codEquiv_ofFn (P : PermFamily) (n : ℕ) (y : Fin (P.toFunFamily.outLen.eval n) → Bool) : List.ofFn (P.toFunFamily_codEquiv n y) = List.ofFn y
ADDED	TCSlib/Cryptography/Asymptotic/OneWay.lean:973	TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv	def	def PermFamily.toFunFamily_domEquiv (P : PermFamily) (n : ℕ) : (Fin (P.toFunFamily.inLen.eval n) → Bool) ≃ (Fin n → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/OneWay.lean:981	TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv_ofFn	theorem	theorem PermFamily.toFunFamily_domEquiv_ofFn (P : PermFamily) (n : ℕ) (x : Fin (P.toFunFamily.inLen.eval n) → Bool) : List.ofFn (P.toFunFamily_domEquiv n x) = List.ofFn x
ADDED	TCSlib/Cryptography/Asymptotic/OneWay.lean:986	TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv_symm_ofFn	theorem	theorem PermFamily.toFunFamily_domEquiv_symm_ofFn (P : PermFamily) (n : ℕ) (x : Fin n → Bool) : List.ofFn ((P.toFunFamily_domEquiv n).symm x) = List.ofFn x
ADDED	TCSlib/Cryptography/Asymptotic/OneWay.lean:995	TCSlib.Cryptography.PermFamily.toFunFamily_f_domEquiv	theorem	theorem PermFamily.toFunFamily_f_domEquiv (P : PermFamily) (n : ℕ) (x : Fin (P.toFunFamily.inLen.eval n) → Bool) : P.toFunFamily_codEquiv n (P.toFunFamily.f n x) = P.f n (P.toFunFamily_domEquiv n x)
ADDED	TCSlib/Cryptography/Asymptotic/OneWay.lean:965	TCSlib.Cryptography.PermFamily.toFunFamily_inLen_eval	theorem	theorem PermFamily.toFunFamily_inLen_eval (P : PermFamily) (n : ℕ) : P.toFunFamily.inLen.eval n = n
ADDED	TCSlib/Cryptography/Asymptotic/OneWay.lean:969	TCSlib.Cryptography.PermFamily.toFunFamily_outLen_eval	theorem	theorem PermFamily.toFunFamily_outLen_eval (P : PermFamily) (n : ℕ) : P.toFunFamily.outLen.eval n = n
ADDED	TCSlib/Cryptography/Asymptotic/OneWay.lean:951	TCSlib.Cryptography.oneWayPermutation_iff	theorem	theorem oneWayPermutation_iff (P : PermFamily) : OneWayPermutation P ↔ P.toFunFamily.StrongOneWay
ADDED	TCSlib/Cryptography/Asymptotic/OneWayYao.lean:588	TCSlib.Cryptography.OneWay.YaoMachine.ρPEquiv	def	def ρPEquiv (n : ℕ) : (Fin ((ρP D).eval n) → Bool) ≃ (Fin (n * D.m.eval n + (D.m.eval n * D.inLen.eval n + D.A'.coinLen n)) → Bool)
ADDED	TCSlib/Cryptography/Asymptotic/OneWayYao.lean:594	TCSlib.Cryptography.OneWay.YaoMachine.ρPEquiv_ofFn	theorem	theorem ρPEquiv_ofFn (n : ℕ) (r : Fin ((ρP D).eval n) → Bool) : List.ofFn (ρPEquiv D n r) = List.ofFn r
ADDED	TCSlib/Cryptography/Asymptotic/OneWayYao.lean:553	TCSlib.Cryptography.OneWay.yaoB_apply	theorem	theorem yaoB_apply (inLen outLen m : PolyExpr) (A' : NUPPT) (n : ℕ) (ys : Fin (m.eval n) → Fin (outLen.eval n) → Bool) (r : A'.Coins n) (j : Fin (m.eval n)) : yaoB inLen outLen m A' n ys r j = padTrue (inLen.eval n) ((A'.runAt n (List.ofFn ((blocksE (m.eval n) (outLen.eval n)).symm ys)) r).drop (j * inLen.eval n))
ADDED	TCSlib/Cryptography/Asymptotic/PublicKey.lean:392	TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncCoins	def	noncomputable def bitwiseEncCoins (S : BitPublicKeyScheme) (n : ℕ) : (Fin n → S.enc.Coins n) ≃ S.bitwise.enc.Coins n
ADDED	TCSlib/Cryptography/Asymptotic/PublicKey.lean:399	TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncCoins_ofFn	theorem	theorem bitwiseEncCoins_ofFn (S : BitPublicKeyScheme) (n : ℕ) (v : Fin n → S.enc.Coins n) : List.ofFn (S.bitwiseEncCoins n v) = List.ofFn (coinBlocks n (S.enc.coinLen n) v)
ADDED	TCSlib/Cryptography/Asymptotic/PublicKey.lean:385	TCSlib.Cryptography.BitPublicKeyScheme.bitwise_enc_coinLen	theorem	theorem bitwise_enc_coinLen (S : BitPublicKeyScheme) (n : ℕ) : n * S.enc.coinLen n = (PolyExpr.mul .var S.enc.coins).eval n
CHANGED	TCSlib/Cryptography/Asymptotic/PublicKey.lean:973->1059	TCSlib.Cryptography.TrapdoorCollection.OneWay.exists_glPad_singleBitSecure	theorem	theorem TrapdoorCollection.OneWay.exists_glPad_singleBitSecure {T : TrapdoorCollection} (m : PolyExpr) (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) (hT : T.OneWay) : ∃ E : (T.glPad m henc).toCollection.PredEvaluator T.glBit, ((T.glPad m henc).tdpBitScheme E).SingleBitSecure	=>	theorem TrapdoorCollection.OneWay.exists_glPad_singleBitSecure {T : TrapdoorCollection} (m : PolyExpr) (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) (hT : T.OneWay) : ∃ E : (T.glPad m henc).toCollection.PredEvaluator fun i z => T.glBit i (T.glPad_domEquiv m henc i z), ((T.glPad m henc).tdpBitScheme E).SingleBitSecure
CHANGED	TCSlib/Cryptography/Asymptotic/PublicKey.lean:959->1041	TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_tdpBitScheme_singleBitSecure	theorem	theorem TrapdoorCollection.OneWay.glPad_tdpBitScheme_singleBitSecure {T : TrapdoorCollection} (m : PolyExpr) (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) (hT : T.OneWay) (E : (T.glPad m henc).toCollection.PredEvaluator T.glBit) : ((T.glPad m henc).tdpBitScheme E).SingleBitSecure	=>	theorem TrapdoorCollection.OneWay.glPad_tdpBitScheme_singleBitSecure {T : TrapdoorCollection} (m : PolyExpr) (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) (hT : T.OneWay) (E : (T.glPad m henc).toCollection.PredEvaluator fun i z => T.glBit i (T.glPad_domEquiv m henc i z)) : ((T.glPad m henc).tdpBitScheme E).SingleBitSecure
ADDED	TCSlib/Cryptography/Asymptotic/PublicKey.lean:679	TCSlib.Cryptography.TrapdoorCollection.coins_tdpEnc	theorem	theorem coins_tdpEnc {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h) : (T.tdpEnc E).coins = T.sample.coins
ADDED	TCSlib/Cryptography/Asymptotic/PublicKey.lean:663	TCSlib.Cryptography.TrapdoorCollection.coins_tdpGen	theorem	theorem coins_tdpGen : T.tdpGen.coins = T.gen.coins
ADDED	TCSlib/Cryptography/Asymptotic/PublicKey.lean:686	TCSlib.Cryptography.TrapdoorCollection.tdpEnc_coinsEquiv	def	noncomputable def tdpEnc_coinsEquiv {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h) (n : ℕ) : (T.tdpEnc E).Coins n ≃ T.sample.Coins n
ADDED	TCSlib/Cryptography/Asymptotic/PublicKey.lean:692	TCSlib.Cryptography.TrapdoorCollection.tdpEnc_coinsEquiv_ofFn	theorem	theorem tdpEnc_coinsEquiv_ofFn {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h) (n : ℕ) (s : (T.tdpEnc E).Coins n) : List.ofFn (T.tdpEnc_coinsEquiv E n s) = List.ofFn s
CHANGED	TCSlib/Cryptography/Asymptotic/PublicKey.lean:647->712	TCSlib.Cryptography.TrapdoorCollection.tdpEnc_runAt	theorem	theorem tdpEnc_runAt {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h) (n : ℕ) (i : List Bool) (b : Bool) (s : T.sample.Coins n) : (T.tdpEnc E).runAt n (pairEncode i [b]) s = pairEncode (T.eval (pairEncode i (T.sample.runAt n i s))) (List.zipWith xor (E.H (pairEncode i (T.sample.runAt n i s))) [b])	=>	theorem tdpEnc_runAt {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h) (n : ℕ) (i : List Bool) (b : Bool) (s : (T.tdpEnc E).Coins n) : (T.tdpEnc E).runAt n (pairEncode i [b]) s = pairEncode (T.eval (pairEncode i (T.sample.runAt n i (T.tdpEnc_coinsEquiv E n s)))) (List.zipWith xor (E.H (pairEncode i (T.sample.runAt n i (T.tdpEnc_coinsEquiv E n s)))) [b])
ADDED	TCSlib/Cryptography/Asymptotic/PublicKey.lean:669	TCSlib.Cryptography.TrapdoorCollection.tdpGen_coinsEquiv	def	noncomputable def tdpGen_coinsEquiv (n : ℕ) : T.tdpGen.Coins n ≃ T.gen.Coins n
ADDED	TCSlib/Cryptography/Asymptotic/PublicKey.lean:674	TCSlib.Cryptography.TrapdoorCollection.tdpGen_coinsEquiv_ofFn	theorem	theorem tdpGen_coinsEquiv_ofFn (n : ℕ) (r : T.tdpGen.Coins n) : List.ofFn (T.tdpGen_coinsEquiv n r) = List.ofFn r
CHANGED	TCSlib/Cryptography/Asymptotic/PublicKey.lean:636->698	TCSlib.Cryptography.TrapdoorCollection.tdpGen_runAt	theorem	theorem tdpGen_runAt (n : ℕ) (r : T.gen.Coins n) : T.tdpGen.runAt n [] r = pairEncode (T.index n r) (pairEncode (List.replicate n true) (pairEncode (T.index n r) (T.trap n r)))	=>	theorem tdpGen_runAt (n : ℕ) (r : T.tdpGen.Coins n) : T.tdpGen.runAt n [] r = pairEncode (T.index n (T.tdpGen_coinsEquiv n r)) (pairEncode (List.replicate n true) (pairEncode (T.index n (T.tdpGen_coinsEquiv n r)) (T.trap n (T.tdpGen_coinsEquiv n r))))
ADDED	TCSlib/Cryptography/Asymptotic/PublicKeyLemmas.lean:560	TCSlib.Cryptography.multiDist_eq	theorem	theorem multiDist_eq (Gen Enc : NUPPT) (n N Lc : ℕ) (m : Fin N → Fin Lc → Bool) (z : Gen.Coins n × (Fin N → Enc.Coins n)) : multiDist Gen Enc n N Lc m z = pairEncode (pairFstD (Gen.runAt n [] z.1)) (encodeList (List.ofFn fun i => Enc.runAt n (pairEncode (pairFstD (Gen.runAt n [] z.1)) (List.ofFn (m i))) (z.2 i)))
CHANGED	TCSlib/Cryptography/Asymptotic/PublicKeyLemmas.lean:760->774	TCSlib.Cryptography.predCoins	def	def predCoins (D : NUPPT) (flip : Bool) (n : ℕ) : Bool × D.Coins n ≃ (tdpPredictor D flip).Coins n	=>	noncomputable def predCoins (D : NUPPT) (flip : Bool) (n : ℕ) : Bool × D.Coins n ≃ (tdpPredictor D flip).Coins n
ADDED	TCSlib/Cryptography/Asymptotic/PublicKeyLemmas.lean:758	TCSlib.Cryptography.tdpPredictor_coinLen	theorem	theorem tdpPredictor_coinLen (D : NUPPT) (n : ℕ) : 1 + D.coinLen n = (PolyExpr.add (.const 1) D.coins).eval n
ADDED	TCSlib/Cryptography/Asymptotic/Sampling.lean:466	TCSlib.Cryptography.firstHit_eq	theorem	theorem firstHit_eq (xs : Fin T → α) : firstHit E xs = (List.finRange T).findSome? fun t => if E (xs t) then some (xs t) else none
ADDED	TCSlib/Cryptography/Asymptotic/Sampling.lean:128	TCSlib.Cryptography.statClose_iff	theorem	theorem statClose_iff (X : σ → γ) (Y : τ → γ) (δ : ℝ) : StatClose X Y δ ↔ ∀ T : γ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ
ADDED	TCSlib/Cryptography/Asymptotic/Universal.lean:251	TCSlib.Cryptography.fUniversal_inLen_eval	theorem	theorem fUniversal_inLen_eval (c : EffectiveMachineCode) (n : ℕ) : (fUniversal c).inLen.eval n = n
CHANGED	TCSlib/Cryptography/Asymptotic/Universal.lean:258->263	TCSlib.Cryptography.ofFn_fUniversal_f	theorem	theorem ofFn_fUniversal_f (c : EffectiveMachineCode) (n : ℕ) (x : Fin n → Bool) : List.ofFn ((fUniversal c).f n x) = (fUniversalStr c (List.ofFn x) ++ List.replicate (univOutLen.eval n) false).take (univOutLen.eval n)	=>	theorem ofFn_fUniversal_f (c : EffectiveMachineCode) (n : ℕ) (x : Fin ((fUniversal c).inLen.eval n) → Bool) : List.ofFn ((fUniversal c).f n x) = (fUniversalStr c (List.ofFn x) ++ List.replicate (univOutLen.eval n) false).take (univOutLen.eval n)
CHANGED	TCSlib/Cryptography/Asymptotic/UniversalPadding.lean:137->137	TCSlib.Cryptography.PadQuad.ofFn_family_f	theorem	theorem ofFn_family_f (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) (m : ℕ) (x : Fin m → Bool) : List.ofFn ((family F ℓ d).f m x) = gStr F ℓ d (List.ofFn x)	=>	theorem ofFn_family_f (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) (m : ℕ) (x : Fin ((family F ℓ d).inLen.eval m) → Bool) : List.ofFn ((family F ℓ d).f m x) = gStr F ℓ d (List.ofFn x)
CHANGED	TCSlib/Cryptography/Asymptotic/UniversalPadding.lean:184->185	TCSlib.Cryptography.PadQuad.quadraticCode_of_linear	theorem	theorem quadraticCode_of_linear {F : List Bool → List Bool} {ℓ : PolyExpr} {d : ℕ} (h : ∃ (M' : FinTM Bool) (c' : ℕ), M'.ComputesFunInTime (gStr F ℓ d) fun m => c' * (m + 1)) : ∃ (Mc : CodeTM) (c₀ : ℕ), ∀ m (x : Fin m → Bool), Mc.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn ((family F ℓ d).f m x)) (c₀ * (m + 1) ^ 2)	=>	theorem quadraticCode_of_linear {F : List Bool → List Bool} {ℓ : PolyExpr} {d : ℕ} (h : ∃ (M' : FinTM Bool) (c' : ℕ), M'.ComputesFunInTime (gStr F ℓ d) fun m => c' * (m + 1)) : ∃ (Mc : CodeTM) (c₀ : ℕ), ∀ m (x : Fin ((family F ℓ d).inLen.eval m) → Bool), Mc.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn ((family F ℓ d).f m x)) (c₀ * (m + 1) ^ 2)
ADDED	TCSlib/Cryptography/Candidates/Arithmetic.lean:346	TCSlib.Cryptography.Candidates.divModStr_pairEncode	theorem	theorem divModStr_pairEncode (a b : List Bool) : divModStr (pairEncode a b) = pairEncode (natToList a.length (listToNat a / listToNat b)) (natToList b.length (listToNat a % listToNat b))
ADDED	TCSlib/Cryptography/Candidates/Arithmetic.lean:92	TCSlib.Cryptography.Candidates.natToList_eq	theorem	theorem natToList_eq (k N : ℕ) : natToList k N = List.ofFn (natToBits k N)
ADDED	TCSlib/Cryptography/Candidates/Arithmetic.lean:297	TCSlib.Cryptography.Candidates.sizeStr_eq	theorem	theorem sizeStr_eq (w : List Bool) : sizeStr w = List.replicate (Nat.size (listToNat w)) true
ADDED	TCSlib/Cryptography/Candidates/Arithmetic.lean:353	TCSlib.Cryptography.Candidates.xgcdStr_pairEncode	theorem	theorem xgcdStr_pairEncode (a b : List Bool) : xgcdStr (pairEncode a b) = pairEncode (natToList b.length (Nat.gcd (listToNat a) (listToNat b))) (natToList b.length ((listToNat a : ZMod (listToNat b))⁻¹).val)
ADDED	TCSlib/Cryptography/Candidates/Concrete.lean:461	TCSlib.Cryptography.Candidates.DistinctPrimes.default_p	theorem	theorem default_p (hn : 2 ≤ n) : (DistinctPrimes.default hn).p = 2
ADDED	TCSlib/Cryptography/Candidates/Concrete.lean:464	TCSlib.Cryptography.Candidates.DistinctPrimes.default_q	theorem	theorem default_q (hn : 2 ≤ n) : (DistinctPrimes.default hn).q = 3
ADDED	TCSlib/Cryptography/Candidates/Concrete.lean:373	TCSlib.Cryptography.Candidates.DistinctPrimes.p_eq	theorem	theorem p_eq (z : DistinctPrimes n) : z.p = ((z.1.1 : Fin (2 ^ n)) : ℕ)
ADDED	TCSlib/Cryptography/Candidates/Concrete.lean:380	TCSlib.Cryptography.Candidates.DistinctPrimes.q_eq	theorem	theorem q_eq (z : DistinctPrimes n) : z.q = ((z.1.2 : Fin (2 ^ n)) : ℕ)
ADDED	TCSlib/Cryptography/Candidates/Concrete.lean:486	TCSlib.Cryptography.Candidates.encodeDistinctPrimes_eq	theorem	theorem encodeDistinctPrimes_eq (m : ℕ) (z : DistinctPrimes m) : encodeDistinctPrimes m z = pairEncode (natToList m z.p) (natToList m z.q)
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:413	TCSlib.Cryptography.Candidates.ExpGroupGen.dlHard_iff	theorem	theorem dlHard_iff : G.DLHard ↔ ∀ A : NUPPT, Negligible fun n => G.dlProb A n
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:397	TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb_eq	theorem	theorem dlProb_eq (A : NUPPT) (n : ℕ) : G.dlProb A n = uexp fun r : G.gen.Coins n => uprob fun z : ZMod (expOrd (G.gen.runAt n [] r)) × A.Coins n => ∃ x : Fin n → Bool, decodeFin n (A.runAt n (pairEncode (G.gen.runAt n [] r) (expF _ z.1)) z.2) = some x ∧ bitsToNat x = z.1.val
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:375	TCSlib.Cryptography.Candidates.ExpGroupGen.fullLengthExcept_iff	theorem	theorem fullLengthExcept_iff (δ : ℕ → ℝ) : G.FullLengthExcept δ ↔ ∀ n, G.n₀ ≤ n → uprob (fun r : G.gen.Coins n => dlP (G.gen.runAt n [] r) < 2 ^ (n - 1)) ≤ δ n
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:942	TCSlib.Cryptography.Candidates.dlCollection_coinsEquiv	def	noncomputable def dlCollection_coinsEquiv (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) : (dlCollection H G).gen.Coins n ≃ G.gen.Coins n
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:948	TCSlib.Cryptography.Candidates.dlCollection_coinsEquiv_ofFn	theorem	theorem dlCollection_coinsEquiv_ofFn (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) (r : (dlCollection H G).gen.Coins n) : List.ofFn (dlCollection_coinsEquiv H G n r) = List.ofFn r
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:921	TCSlib.Cryptography.Candidates.dlCollection_decD	theorem	theorem dlCollection_decD (H : ArithmeticFP) (G : SafePrimeGen) (i w : List Bool) : (dlCollection H G).decD i w = (expDec i w).map (dlCollection_domEquiv H G i).symm
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:893	TCSlib.Cryptography.Candidates.dlCollection_domEquiv	def	def dlCollection_domEquiv (H : ArithmeticFP) (G : SafePrimeGen) (i : List Bool) : (dlCollection H G).D i ≃ ZMod (expOrd i)
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:900	TCSlib.Cryptography.Candidates.dlCollection_domEquiv_uprob	theorem	theorem dlCollection_domEquiv_uprob (H : ArithmeticFP) (G : SafePrimeGen) (i : List Bool) (P : ZMod (expOrd i) → Prop) : uprob (fun x : (dlCollection H G).D i => P (dlCollection_domEquiv H G i x)) = uprob P
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:914	TCSlib.Cryptography.Candidates.dlCollection_encD	theorem	theorem dlCollection_encD (H : ArithmeticFP) (G : SafePrimeGen) (i : List Bool) (x : (dlCollection H G).D i) : (dlCollection H G).encD i x = expEnc i (dlCollection_domEquiv H G i x)
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:936	TCSlib.Cryptography.Candidates.dlCollection_eval	theorem	theorem dlCollection_eval (H : ArithmeticFP) (G : SafePrimeGen) : (dlCollection H G).eval = expEval
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:907	TCSlib.Cryptography.Candidates.dlCollection_f	theorem	theorem dlCollection_f (H : ArithmeticFP) (G : SafePrimeGen) (i : List Bool) (x : (dlCollection H G).D i) : (dlCollection H G).f i x = expF i (dlCollection_domEquiv H G i x)
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:926	TCSlib.Cryptography.Candidates.dlCollection_gen	theorem	theorem dlCollection_gen (H : ArithmeticFP) (G : SafePrimeGen) : (dlCollection H G).gen = expGen G
CHANGED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:702->955	TCSlib.Cryptography.Candidates.dlCollection_index	theorem	theorem dlCollection_index (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) (r : G.gen.Coins n) (hn : G.n₀ ≤ n) : (dlCollection H G).index n r = G.gen.runAt n [] r	=>	theorem dlCollection_index (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) (r : (dlCollection H G).gen.Coins n) (hn : G.n₀ ≤ n) : (dlCollection H G).index n r = G.gen.runAt n [] (dlCollection_coinsEquiv H G n r)
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:931	TCSlib.Cryptography.Candidates.dlCollection_sample	theorem	theorem dlCollection_sample (H : ArithmeticFP) (G : SafePrimeGen) : (dlCollection H G).sample = expSampler H
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:137	TCSlib.Cryptography.Candidates.dlG_eq	theorem	theorem dlG_eq (i : List Bool) : dlG i = listToNat (pairSndD (pairSndD i))
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:130	TCSlib.Cryptography.Candidates.dlM_eq	theorem	theorem dlM_eq (i : List Bool) : dlM i = listToNat (pairFstD (pairSndD i))
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:122	TCSlib.Cryptography.Candidates.dlP_eq	theorem	theorem dlP_eq (i : List Bool) : dlP i = listToNat (pairFstD i)
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:750	TCSlib.Cryptography.Candidates.expCollection_coinsEquiv	def	noncomputable def expCollection_coinsEquiv {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (n : ℕ) : (expCollection H G hV).gen.Coins n ≃ G.gen.Coins n
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:765	TCSlib.Cryptography.Candidates.expCollection_coinsEquiv_uexp	theorem	theorem expCollection_coinsEquiv_uexp {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (n : ℕ) (F : G.gen.Coins n → ℝ) : uexp (fun r : (expCollection H G hV).gen.Coins n => F (expCollection_coinsEquiv H G hV n r)) = uexp F
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:757	TCSlib.Cryptography.Candidates.expCollection_coinsEquiv_uprob	theorem	theorem expCollection_coinsEquiv_uprob {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (n : ℕ) (P : G.gen.Coins n → Prop) : uprob (fun r : (expCollection H G hV).gen.Coins n => P (expCollection_coinsEquiv H G hV n r)) = uprob P
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:728	TCSlib.Cryptography.Candidates.expCollection_decD	theorem	theorem expCollection_decD {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (i w : List Bool) : (expCollection H G hV).decD i w = (expDec i w).map (expCollection_domEquiv H G hV i).symm
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:699	TCSlib.Cryptography.Candidates.expCollection_domEquiv	def	def expCollection_domEquiv {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (i : List Bool) : (expCollection H G hV).D i ≃ ZMod (expOrd i)
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:707	TCSlib.Cryptography.Candidates.expCollection_domEquiv_uprob	theorem	theorem expCollection_domEquiv_uprob {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (i : List Bool) (P : ZMod (expOrd i) → Prop) : uprob (fun x : (expCollection H G hV).D i => P (expCollection_domEquiv H G hV i x)) = uprob P
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:721	TCSlib.Cryptography.Candidates.expCollection_encD	theorem	theorem expCollection_encD {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (i : List Bool) (x : (expCollection H G hV).D i) : (expCollection H G hV).encD i x = expEnc i (expCollection_domEquiv H G hV i x)
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:743	TCSlib.Cryptography.Candidates.expCollection_eval	theorem	theorem expCollection_eval {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) : (expCollection H G hV).eval = expEval
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:715	TCSlib.Cryptography.Candidates.expCollection_f	theorem	theorem expCollection_f {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (i : List Bool) (x : (expCollection H G hV).D i) : (expCollection H G hV).f i x = expF i (expCollection_domEquiv H G hV i x)
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:735	TCSlib.Cryptography.Candidates.expCollection_gen	theorem	theorem expCollection_gen {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) : (expCollection H G hV).gen = expGen G
CHANGED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:593->773	TCSlib.Cryptography.Candidates.expCollection_index	theorem	theorem expCollection_index {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (n : ℕ) (r : G.gen.Coins n) (hn : G.n₀ ≤ n) : (expCollection H G hV).index n r = G.gen.runAt n [] r	=>	theorem expCollection_index {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (n : ℕ) (r : (expCollection H G hV).gen.Coins n) (hn : G.n₀ ≤ n) : (expCollection H G hV).index n r = G.gen.runAt n [] (expCollection_coinsEquiv H G hV n r)
CHANGED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:600->781	TCSlib.Cryptography.Candidates.expCollection_index_of_lt	theorem	theorem expCollection_index_of_lt {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (n : ℕ) (r : G.gen.Coins n) (hn : n < G.n₀) : (expCollection H G hV).index n r = dlDefaultIndex	=>	theorem expCollection_index_of_lt {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (n : ℕ) (r : (expCollection H G hV).gen.Coins n) (hn : n < G.n₀) : (expCollection H G hV).index n r = dlDefaultIndex
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:739	TCSlib.Cryptography.Candidates.expCollection_sample	theorem	theorem expCollection_sample {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) : (expCollection H G hV).sample = expSampler H
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:238	TCSlib.Cryptography.Candidates.expEnc_eq	theorem	theorem expEnc_eq (i : List Bool) (x : ZMod (expOrd i)) : expEnc i x = natToList (dlW i) x.val
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:268	TCSlib.Cryptography.Candidates.expF_eq	theorem	theorem expF_eq (i : List Bool) (x : ZMod (expOrd i)) : expF i x = natToList (dlW i) (dlG i ^ x.val % dlP i)
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:520	TCSlib.Cryptography.Candidates.expGen_coinLen	theorem	theorem expGen_coinLen {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ) : (expGen G).coinLen n = G.gen.coinLen n
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:513	TCSlib.Cryptography.Candidates.expGen_coins	theorem	theorem expGen_coins {V : List Bool → Prop} (G : ExpGroupGen V) : (expGen G).coins = G.gen.coins
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:528	TCSlib.Cryptography.Candidates.expGen_coinsEquiv	def	noncomputable def expGen_coinsEquiv {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ) : (expGen G).Coins n ≃ G.gen.Coins n
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:534	TCSlib.Cryptography.Candidates.expGen_coinsEquiv_ofFn	theorem	theorem expGen_coinsEquiv_ofFn {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ) (r : (expGen G).Coins n) : List.ofFn (expGen_coinsEquiv G n r) = List.ofFn r
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:549	TCSlib.Cryptography.Candidates.expGen_coinsEquiv_uexp	theorem	theorem expGen_coinsEquiv_uexp {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ) (F : G.gen.Coins n → ℝ) : uexp (fun r : (expGen G).Coins n => F (expGen_coinsEquiv G n r)) = uexp F
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:541	TCSlib.Cryptography.Candidates.expGen_coinsEquiv_uprob	theorem	theorem expGen_coinsEquiv_uprob {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ) (P : G.gen.Coins n → Prop) : uprob (fun r : (expGen G).Coins n => P (expGen_coinsEquiv G n r)) = uprob P
CHANGED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:454->556	TCSlib.Cryptography.Candidates.expGen_runAt	theorem	theorem expGen_runAt {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ) (r : G.gen.Coins n) : (expGen G).runAt n [] r = if G.n₀ ≤ n then pairEncode (G.gen.runAt n [] r) [] else pairEncode dlDefaultIndex []	=>	theorem expGen_runAt {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ) (r : (expGen G).Coins n) : (expGen G).runAt n [] r = if G.n₀ ≤ n then pairEncode (G.gen.runAt n [] (expGen_coinsEquiv G n r)) [] else pairEncode dlDefaultIndex []
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:180	TCSlib.Cryptography.Candidates.expValid_iff	theorem	theorem expValid_iff (i : List Bool) : ExpValid i ↔ (dlP i).Prime ∧ 0 < dlM i ∧ dlM i < dlP i ∧ 0 < dlG i ∧ dlG i < dlP i ∧ orderOf ((dlG i : ℕ) : ZMod (dlP i)) = dlM i
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:854	TCSlib.Cryptography.Candidates.safePrimeValid_iff	theorem	theorem safePrimeValid_iff (i : List Bool) : SafePrimeValid i ↔ ExpValid i ∧ (dlM i).Prime ∧ dlP i = 2 * dlM i + 1
ADDED	TCSlib/Cryptography/Candidates/DiscreteLog.lean:150	TCSlib.Cryptography.Candidates.wellFormedIndex_iff	theorem	theorem wellFormedIndex_iff (n : ℕ) (i : List Bool) : WellFormedIndex n i ↔ ∃ a b c : List Bool, i = pairEncode a (pairEncode b c) ∧ a.length = n ∧ b.length = n ∧ c.length = n
ADDED	TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:487	TCSlib.Cryptography.Candidates.fullDLAssumption_iff	theorem	theorem fullDLAssumption_iff (G : FullGroupGen) : FullDLAssumption G ↔ ∀ A : NUPPT, Negligible fun n => G.dlProb A n
ADDED	TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:543	TCSlib.Cryptography.Candidates.fullDLCollection_coinsEquiv	def	noncomputable def fullDLCollection_coinsEquiv (H : ArithmeticFP) (G : FullGroupGen) (n : ℕ) : (fullDLCollection H G).gen.Coins n ≃ G.gen.Coins n
ADDED	TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:557	TCSlib.Cryptography.Candidates.fullDLCollection_coinsEquiv_uexp	theorem	theorem fullDLCollection_coinsEquiv_uexp (H : ArithmeticFP) (G : FullGroupGen) (n : ℕ) (F : G.gen.Coins n → ℝ) : uexp (fun r : (fullDLCollection H G).gen.Coins n => F (fullDLCollection_coinsEquiv H G n r)) = uexp F
ADDED	TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:549	TCSlib.Cryptography.Candidates.fullDLCollection_coinsEquiv_uprob	theorem	theorem fullDLCollection_coinsEquiv_uprob (H : ArithmeticFP) (G : FullGroupGen) (n : ℕ) (P : G.gen.Coins n → Prop) : uprob (fun r : (fullDLCollection H G).gen.Coins n => P (fullDLCollection_coinsEquiv H G n r)) = uprob P
ADDED	TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:530	TCSlib.Cryptography.Candidates.fullDLCollection_decD	theorem	theorem fullDLCollection_decD (H : ArithmeticFP) (G : FullGroupGen) (i w : List Bool) : (fullDLCollection H G).decD i w = (expDec i w).map (fullDLCollection_domEquiv H G i).symm
ADDED	TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:501	TCSlib.Cryptography.Candidates.fullDLCollection_domEquiv	def	def fullDLCollection_domEquiv (H : ArithmeticFP) (G : FullGroupGen) (i : List Bool) : (fullDLCollection H G).D i ≃ ZMod (expOrd i)
ADDED	TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:508	TCSlib.Cryptography.Candidates.fullDLCollection_domEquiv_uprob	theorem	theorem fullDLCollection_domEquiv_uprob (H : ArithmeticFP) (G : FullGroupGen) (i : List Bool) (P : ZMod (expOrd i) → Prop) : uprob (fun x : (fullDLCollection H G).D i => P (fullDLCollection_domEquiv H G i x)) = uprob P
ADDED	TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:522	TCSlib.Cryptography.Candidates.fullDLCollection_encD	theorem	theorem fullDLCollection_encD (H : ArithmeticFP) (G : FullGroupGen) (i : List Bool) (x : (fullDLCollection H G).D i) : (fullDLCollection H G).encD i x = expEnc i (fullDLCollection_domEquiv H G i x)
ADDED	TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:576	TCSlib.Cryptography.Candidates.fullDLCollection_eval	theorem	theorem fullDLCollection_eval (H : ArithmeticFP) (G : FullGroupGen) : (fullDLCollection H G).eval = expEval
ADDED	TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:515	TCSlib.Cryptography.Candidates.fullDLCollection_f	theorem	theorem fullDLCollection_f (H : ArithmeticFP) (G : FullGroupGen) (i : List Bool) (x : (fullDLCollection H G).D i) : (fullDLCollection H G).f i x = expF i (fullDLCollection_domEquiv H G i x)
ADDED	TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:535	TCSlib.Cryptography.Candidates.fullDLCollection_gen	theorem	theorem fullDLCollection_gen (H : ArithmeticFP) (G : FullGroupGen) : (fullDLCollection H G).gen = expGen G
CHANGED	TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:592->692	TCSlib.Cryptography.Candidates.fullDLCollection_hardCore	theorem	theorem fullDLCollection_hardCore (H : ArithmeticFP) (G : FullGroupGen) (hbig : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ) (hDL : FullDLAssumption G) : (fullDLCollection H G).HardCore halfPred	=>	theorem fullDLCollection_hardCore (H : ArithmeticFP) (G : FullGroupGen) (hbig : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ) (hDL : FullDLAssumption G) : (fullDLCollection H G).HardCore fun i x => halfPred i (fullDLCollection_domEquiv H G i x)
ADDED	TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:565	TCSlib.Cryptography.Candidates.fullDLCollection_index	theorem	theorem fullDLCollection_index (H : ArithmeticFP) (G : FullGroupGen) (n : ℕ) (r : (fullDLCollection H G).gen.Coins n) (hn : G.n₀ ≤ n) : (fullDLCollection H G).index n r = G.gen.runAt n [] (fullDLCollection_coinsEquiv H G n r)
ADDED	TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:571	TCSlib.Cryptography.Candidates.fullDLCollection_sample	theorem	theorem fullDLCollection_sample (H : ArithmeticFP) (G : FullGroupGen) : (fullDLCollection H G).sample = expSampler H
ADDED	TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:465	TCSlib.Cryptography.Candidates.fullGroupValid_iff	theorem	theorem fullGroupValid_iff (i : List Bool) : FullGroupValid i ↔ ExpValid i ∧ dlM i = dlP i - 1 ∧ dlP i % 4 = 3
ADDED	TCSlib/Cryptography/Candidates/ElGamal.lean:332	TCSlib.Cryptography.Candidates.ddhAssumption_iff	theorem	theorem ddhAssumption_iff (G : SafePrimeGen) : DDHAssumption G ↔ (ddhReal G).Indist (ddhRandom G)
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:829	TCSlib.Cryptography.Candidates.collectionFactorer_coinsEquiv	def	noncomputable def collectionFactorer_coinsEquiv (A : NUPPT) (n : ℕ) : (collectionFactorer A).Coins n ≃ A.Coins n
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:835	TCSlib.Cryptography.Candidates.collectionFactorer_coinsEquiv_ofFn	theorem	theorem collectionFactorer_coinsEquiv_ofFn (A : NUPPT) (n : ℕ) (r : (collectionFactorer A).Coins n) : List.ofFn (collectionFactorer_coinsEquiv A n r) = List.ofFn r
CHANGED	TCSlib/Cryptography/Candidates/Factoring.lean:653->842	TCSlib.Cryptography.Candidates.collectionFactorer_runAt	theorem	theorem collectionFactorer_runAt (A : NUPPT) (n : ℕ) (y : List Bool) (r : (collectionFactorer A).Coins n) : (collectionFactorer A).runAt n y r = pairFstD (A.runAt n (pairEncode (List.replicate n true) y) r)	=>	theorem collectionFactorer_runAt (A : NUPPT) (n : ℕ) (y : List Bool) (r : (collectionFactorer A).Coins n) : (collectionFactorer A).runAt n y r = pairFstD (A.runAt n (pairEncode (List.replicate n true) y) (collectionFactorer_coinsEquiv A n r))
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:233	TCSlib.Cryptography.Candidates.factorProb_eq	theorem	theorem factorProb_eq (A : NUPPT) (n : ℕ) : factorProb A n = uprob fun w : DistinctPrimes n × A.Coins n => ∃ x : Fin n → Bool, A.inverter n n (2 * n) (modulusBits n w.1) w.2 = some x ∧ (bitsToNat x = w.1.p ∨ bitsToNat x = w.1.q)
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:248	TCSlib.Cryptography.Candidates.factoringAssumption_iff	theorem	theorem factoringAssumption_iff : FactoringAssumption ↔ ∀ A : NUPPT, Negligible fun n => factorProb A n
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:756	TCSlib.Cryptography.Candidates.factoringCollection_decD	theorem	theorem factoringCollection_decD (H : ArithmeticFP) (i w : List Bool) : (factoringCollection H).decD i w = (decodeDistinctPrimes (max i.length 2) w).map (factoringCollection_domEquiv H i).symm
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:724	TCSlib.Cryptography.Candidates.factoringCollection_domEquiv	def	def factoringCollection_domEquiv (H : ArithmeticFP) (i : List Bool) : (factoringCollection H).D i ≃ DistinctPrimes (max i.length 2)
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:732	TCSlib.Cryptography.Candidates.factoringCollection_domEquiv_uprob	theorem	theorem factoringCollection_domEquiv_uprob (H : ArithmeticFP) (i : List Bool) (P : DistinctPrimes (max i.length 2) → Prop) : uprob (fun x : (factoringCollection H).D i => P (factoringCollection_domEquiv H i x)) = uprob P
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:748	TCSlib.Cryptography.Candidates.factoringCollection_encD	theorem	theorem factoringCollection_encD (H : ArithmeticFP) (i : List Bool) (x : (factoringCollection H).D i) : (factoringCollection H).encD i x = encodeDistinctPrimes (max i.length 2) (factoringCollection_domEquiv H i x)
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:772	TCSlib.Cryptography.Candidates.factoringCollection_eval	theorem	theorem factoringCollection_eval (H : ArithmeticFP) (z : List Bool) : (factoringCollection H).eval z = mulStr (pairSndD z)
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:741	TCSlib.Cryptography.Candidates.factoringCollection_f	theorem	theorem factoringCollection_f (H : ArithmeticFP) (i : List Bool) (x : (factoringCollection H).D i) : (factoringCollection H).f i x = natToList (2 * max i.length 2) ((factoringCollection_domEquiv H i x).p * (factoringCollection_domEquiv H i x).q)
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:763	TCSlib.Cryptography.Candidates.factoringCollection_gen	theorem	theorem factoringCollection_gen (H : ArithmeticFP) : (factoringCollection H).gen = factoringGen
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:767	TCSlib.Cryptography.Candidates.factoringCollection_sample	theorem	theorem factoringCollection_sample (H : ArithmeticFP) : (factoringCollection H).sample = factoringSampler H
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:373	TCSlib.Cryptography.Candidates.fmult_prod_outLen	theorem	theorem fmult_prod_outLen (n : ℕ) : (fmult.prod fmultBlocks).outLen.eval n = 4 * n ^ 3 * (2 * n)
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:208	TCSlib.Cryptography.Candidates.modulusBits_eq	theorem	theorem modulusBits_eq (n : ℕ) (z : DistinctPrimes n) : modulusBits n z = natToBits (2 * n) (z.p * z.q)
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:299	TCSlib.Cryptography.Candidates.oneCallFactorer_coinsEquiv	def	noncomputable def oneCallFactorer_coinsEquiv (A : NUPPT) (n : ℕ) : (oneCallFactorer A).Coins n ≃ A.Coins n
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:305	TCSlib.Cryptography.Candidates.oneCallFactorer_coinsEquiv_ofFn	theorem	theorem oneCallFactorer_coinsEquiv_ofFn (A : NUPPT) (n : ℕ) (r : (oneCallFactorer A).Coins n) : List.ofFn (oneCallFactorer_coinsEquiv A n r) = List.ofFn r
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:536	TCSlib.Cryptography.Candidates.polyTimeComputable_samplePrimeL	theorem	theorem polyTimeComputable_samplePrimeL (hP : PolyTimeComputable primeStr) : PolyTimeComputable fun z => samplePrimeL (pairFstD z).length (pairSndD z)
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:392	TCSlib.Cryptography.Candidates.prodInverter_eq	theorem	theorem prodInverter_eq (A : NUPPT) (n : ℕ) (ys : Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) (r : A.Coins n) : prodInverter A n ys r = FunFamily.blocks (fmultBlocks.eval n) (2 * n) ((A.inverter n (fmultBlocks.eval n * (2 * n)) (fmultBlocks.eval n * (2 * n)) ((FunFamily.blocks (fmultBlocks.eval n) (2 * n)).symm ys) r).getD (fun _ => false))
ADDED	TCSlib/Cryptography/Candidates/Factoring.lean:564	TCSlib.Cryptography.Candidates.statClose_samplePrimeL_pair	theorem	theorem statClose_samplePrimeL_pair (n : ℕ) (hn : 2 ≤ n) : StatClose (fun s : Fin (2 * (2 * n ^ 2 * n)) → Bool => (listToNat (samplePrimeL n ((List.ofFn s).take (2 * n ^ 2 * n))), listToNat (samplePrimeL n ((List.ofFn s).drop (2 * n ^ 2 * n))))) (fun z : DistinctPrimes n => (z.p, z.q)) (2 * (1 / 2 : ℝ) ^ n + 2 * n / 2 ^ n)
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:350	TCSlib.Cryptography.Candidates.eval_rsaBlock	theorem	theorem eval_rsaBlock (n : ℕ) : rsaBlock.eval n = 2 * (n + 2)
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:364	TCSlib.Cryptography.Candidates.eval_rsaSampleCoins	theorem	theorem eval_rsaSampleCoins (n : ℕ) : rsaSampleCoins.eval n = rsaTrials.eval n * rsaBlock.eval n
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:358	TCSlib.Cryptography.Candidates.eval_rsaTrials	theorem	theorem eval_rsaTrials (n : ℕ) : rsaTrials.eval n = (4 * n + 8) * n
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:121	TCSlib.Cryptography.Candidates.rsaAssumption_iff	theorem	theorem rsaAssumption_iff : RSAAssumption ↔ ∀ A : NUPPT, Negligible fun n => rsaProb A n
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:906	TCSlib.Cryptography.Candidates.rsaBreaker_coinsEquiv	def	noncomputable def rsaBreaker_coinsEquiv (A : NUPPT) (n : ℕ) : (rsaBreaker A).Coins n ≃ A.Coins n
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:911	TCSlib.Cryptography.Candidates.rsaBreaker_coinsEquiv_ofFn	theorem	theorem rsaBreaker_coinsEquiv_ofFn (A : NUPPT) (n : ℕ) (r : (rsaBreaker A).Coins n) : List.ofFn (rsaBreaker_coinsEquiv A n r) = List.ofFn r
CHANGED	TCSlib/Cryptography/Candidates/RSA.lean:738->918	TCSlib.Cryptography.Candidates.rsaBreaker_runAt	theorem	theorem rsaBreaker_runAt (A : NUPPT) (n : ℕ) (N e y : List Bool) (r : (rsaBreaker A).Coins n) : (rsaBreaker A).runAt n (pairEncode N (pairEncode e y)) r = A.runAt n (pairEncode (pairEncode N e) y) r	=>	theorem rsaBreaker_runAt (A : NUPPT) (n : ℕ) (N e y : List Bool) (r : (rsaBreaker A).Coins n) : (rsaBreaker A).runAt n (pairEncode N (pairEncode e y)) r = A.runAt n (pairEncode (pairEncode N e) y) (rsaBreaker_coinsEquiv A n r)
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:815	TCSlib.Cryptography.Candidates.rsaCollection_decD	theorem	theorem rsaCollection_decD (H : ArithmeticFP) (i w : List Bool) : (rsaCollection H).decD i w = (rsaDec i w).map (rsaCollection_domEquiv H i).symm
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:791	TCSlib.Cryptography.Candidates.rsaCollection_domEquiv	def	def rsaCollection_domEquiv (H : ArithmeticFP) (i : List Bool) : (rsaCollection H).D i ≃ (ZMod (rsaMod i))ˣ
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:798	TCSlib.Cryptography.Candidates.rsaCollection_domEquiv_uprob	theorem	theorem rsaCollection_domEquiv_uprob (H : ArithmeticFP) (i : List Bool) (P : (ZMod (rsaMod i))ˣ → Prop) : uprob (fun x : (rsaCollection H).D i => P (rsaCollection_domEquiv H i x)) = uprob P
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:810	TCSlib.Cryptography.Candidates.rsaCollection_encD	theorem	theorem rsaCollection_encD (H : ArithmeticFP) (i : List Bool) (x : (rsaCollection H).D i) : (rsaCollection H).encD i x = rsaEnc i (rsaCollection_domEquiv H i x)
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:826	TCSlib.Cryptography.Candidates.rsaCollection_eval	theorem	theorem rsaCollection_eval (H : ArithmeticFP) : (rsaCollection H).eval = rsaEval
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:805	TCSlib.Cryptography.Candidates.rsaCollection_f	theorem	theorem rsaCollection_f (H : ArithmeticFP) (i : List Bool) (x : (rsaCollection H).D i) : (rsaCollection H).f i x = rsaF i (rsaCollection_domEquiv H i x)
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:820	TCSlib.Cryptography.Candidates.rsaCollection_gen	theorem	theorem rsaCollection_gen (H : ArithmeticFP) : (rsaCollection H).gen = rsaGen H
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:823	TCSlib.Cryptography.Candidates.rsaCollection_sample	theorem	theorem rsaCollection_sample (H : ArithmeticFP) : (rsaCollection H).sample = rsaSampler H
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:1076	TCSlib.Cryptography.Candidates.rsaFromFactorer_coinsEquiv	def	noncomputable def rsaFromFactorer_coinsEquiv (H : ArithmeticFP) (A : NUPPT) (n : ℕ) : (rsaFromFactorer H A).Coins n ≃ A.Coins n
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:1082	TCSlib.Cryptography.Candidates.rsaFromFactorer_coinsEquiv_ofFn	theorem	theorem rsaFromFactorer_coinsEquiv_ofFn (H : ArithmeticFP) (A : NUPPT) (n : ℕ) (r : (rsaFromFactorer H A).Coins n) : List.ofFn (rsaFromFactorer_coinsEquiv H A n r) = List.ofFn r
CHANGED	TCSlib/Cryptography/Candidates/RSA.lean:891->1089	TCSlib.Cryptography.Candidates.rsaFromFactorer_runAt	theorem	theorem rsaFromFactorer_runAt (H : ArithmeticFP) (A : NUPPT) (n : ℕ) (N e y : List Bool) (r : (rsaFromFactorer H A).Coins n) : (rsaFromFactorer H A).runAt n (pairEncode N (pairEncode e y)) r = rsaFromFactorStep n (A.runAt n N r) (listToNat N) (listToNat e) (listToNat y)	=>	theorem rsaFromFactorer_runAt (H : ArithmeticFP) (A : NUPPT) (n : ℕ) (N e y : List Bool) (r : (rsaFromFactorer H A).Coins n) : (rsaFromFactorer H A).runAt n (pairEncode N (pairEncode e y)) r = rsaFromFactorStep n (A.runAt n N (rsaFromFactorer_coinsEquiv H A n r)) (listToNat N) (listToNat e) (listToNat y)
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:760	TCSlib.Cryptography.Candidates.rsaTrapdoor_decD	theorem	theorem rsaTrapdoor_decD (H : ArithmeticFP) (i w : List Bool) : (rsaTrapdoor H).decD i w = (rsaDec i w).map (rsaTrapdoor_domEquiv H i).symm
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:736	TCSlib.Cryptography.Candidates.rsaTrapdoor_domEquiv	def	def rsaTrapdoor_domEquiv (H : ArithmeticFP) (i : List Bool) : (rsaTrapdoor H).D i ≃ (ZMod (rsaMod i))ˣ
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:743	TCSlib.Cryptography.Candidates.rsaTrapdoor_domEquiv_uprob	theorem	theorem rsaTrapdoor_domEquiv_uprob (H : ArithmeticFP) (i : List Bool) (P : (ZMod (rsaMod i))ˣ → Prop) : uprob (fun x : (rsaTrapdoor H).D i => P (rsaTrapdoor_domEquiv H i x)) = uprob P
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:755	TCSlib.Cryptography.Candidates.rsaTrapdoor_encD	theorem	theorem rsaTrapdoor_encD (H : ArithmeticFP) (i : List Bool) (x : (rsaTrapdoor H).D i) : (rsaTrapdoor H).encD i x = rsaEnc i (rsaTrapdoor_domEquiv H i x)
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:779	TCSlib.Cryptography.Candidates.rsaTrapdoor_eval	theorem	theorem rsaTrapdoor_eval (H : ArithmeticFP) : (rsaTrapdoor H).eval = rsaEval
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:750	TCSlib.Cryptography.Candidates.rsaTrapdoor_f	theorem	theorem rsaTrapdoor_f (H : ArithmeticFP) (i : List Bool) (x : (rsaTrapdoor H).D i) : (rsaTrapdoor H).f i x = rsaF i (rsaTrapdoor_domEquiv H i x)
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:773	TCSlib.Cryptography.Candidates.rsaTrapdoor_gen	theorem	theorem rsaTrapdoor_gen (H : ArithmeticFP) : (rsaTrapdoor H).gen = rsaGen H
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:782	TCSlib.Cryptography.Candidates.rsaTrapdoor_inv	theorem	theorem rsaTrapdoor_inv (H : ArithmeticFP) : (rsaTrapdoor H).inv = rsaInv H
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:768	TCSlib.Cryptography.Candidates.rsaTrapdoor_perm	theorem	theorem rsaTrapdoor_perm (H : ArithmeticFP) (i : List Bool) (x : (rsaTrapdoor H).D i) : (rsaTrapdoor H).perm i x = (rsaTrapdoor_domEquiv H i).symm (rsaPermAt i (rsaTrapdoor_domEquiv H i x))
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:776	TCSlib.Cryptography.Candidates.rsaTrapdoor_sample	theorem	theorem rsaTrapdoor_sample (H : ArithmeticFP) : (rsaTrapdoor H).sample = rsaSampler H
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:200	TCSlib.Cryptography.Candidates.rsaValid_iff	theorem	theorem rsaValid_iff (i : List Bool) : RSAValid i ↔ rsaN i ≠ 0 ∧ Nat.Coprime (rsaE i) (Nat.totient (rsaN i))
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:383	TCSlib.Cryptography.Candidates.sampleUnitL_eq	theorem	theorem sampleUnitL_eq (N k B T : ℕ) (r : List Bool) : sampleUnitL N k B T r = rejectBlocksL (fun v => v < N ∧ Nat.Coprime v N) k B T r
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:415	TCSlib.Cryptography.Candidates.statClose_sampleUnitL	theorem	theorem statClose_sampleUnitL (n N : ℕ) [NeZero N] (hk : Nat.size N ≤ rsaBlock.eval n) : StatClose (fun s : Fin (rsaSampleCoins.eval n) → Bool => (sampleUnitL N (Nat.size N) (rsaBlock.eval n) (rsaTrials.eval n) (List.ofFn s)).getD (1 % N)) (fun x : (ZMod N)ˣ => (x : ZMod N).val) (Real.exp (-(n : ℝ)))
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:434	TCSlib.Cryptography.Candidates.unitSampleStr_eq	theorem	theorem unitSampleStr_eq (w : List Bool) (n : ℕ) (r : List Bool) : unitSampleStr w n r = natToList w.length ((sampleUnitL (listToNat w) (Nat.size (listToNat w)) (rsaBlock.eval n) (rsaTrials.eval n) r).getD (1 % listToNat w))
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:114	TCSlib.Cryptography.Candidates.blumFactoringAssumption_iff	theorem	theorem blumFactoringAssumption_iff : BlumFactoringAssumption ↔ ∀ A : NUPPT, Negligible fun n => blumFactorProb A n
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:707	TCSlib.Cryptography.Candidates.blumValid_iff	theorem	theorem blumValid_iff (i : List Bool) : BlumValid i ↔ ∃ p ∈ Finset.range (listToNat i), ∃ q ∈ Finset.range (listToNat i), p.Prime ∧ q.Prime ∧ p ≠ q ∧ p % 4 = 3 ∧ q % 4 = 3 ∧ listToNat i = p * q
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:1087	TCSlib.Cryptography.Candidates.coins_rabinBlumInverter	theorem	theorem coins_rabinBlumInverter (H : ArithmeticFP) (A : NUPPT) : (rabinBlumInverter H A).coins = A.coins
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:1095	TCSlib.Cryptography.Candidates.rabinBlumInverter_coinsEquiv	def	noncomputable def rabinBlumInverter_coinsEquiv (H : ArithmeticFP) (A : NUPPT) (n : ℕ) : (rabinBlumInverter H A).Coins n ≃ A.Coins n
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:1101	TCSlib.Cryptography.Candidates.rabinBlumInverter_coinsEquiv_ofFn	theorem	theorem rabinBlumInverter_coinsEquiv_ofFn (H : ArithmeticFP) (A : NUPPT) (n : ℕ) (r : (rabinBlumInverter H A).Coins n) : List.ofFn (rabinBlumInverter_coinsEquiv H A n r) = List.ofFn r
CHANGED	TCSlib/Cryptography/Candidates/Rabin.lean:959->1108	TCSlib.Cryptography.Candidates.rabinBlumInverter_runAt	theorem	theorem rabinBlumInverter_runAt (H : ArithmeticFP) (A : NUPPT) (n : ℕ) (N y : List Bool) (r : (rabinBlumInverter H A).Coins n) : (rabinBlumInverter H A).runAt n (pairEncode N y) r = rabinRootStep (A.runAt n N r) (listToNat N) y	=>	theorem rabinBlumInverter_runAt (H : ArithmeticFP) (A : NUPPT) (n : ℕ) (N y : List Bool) (r : (rabinBlumInverter H A).Coins n) : (rabinBlumInverter H A).runAt n (pairEncode N y) r = rabinRootStep (A.runAt n N (rabinBlumInverter_coinsEquiv H A n r)) (listToNat N) y
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:980	TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_decD	theorem	theorem rabinBlumTrapdoor_decD (H : ArithmeticFP) (i w : List Bool) : (rabinBlumTrapdoor H).decD i w = (blumDec i w).map (rabinBlumTrapdoor_domEquiv H i).symm
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:954	TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_domEquiv	def	def rabinBlumTrapdoor_domEquiv (H : ArithmeticFP) (i : List Bool) : (rabinBlumTrapdoor H).D i ≃ QR (blumMod i)
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:961	TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_domEquiv_uprob	theorem	theorem rabinBlumTrapdoor_domEquiv_uprob (H : ArithmeticFP) (i : List Bool) (P : QR (blumMod i) → Prop) : uprob (fun x : (rabinBlumTrapdoor H).D i => P (rabinBlumTrapdoor_domEquiv H i x)) = uprob P
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:973	TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_encD	theorem	theorem rabinBlumTrapdoor_encD (H : ArithmeticFP) (i : List Bool) (x : (rabinBlumTrapdoor H).D i) : (rabinBlumTrapdoor H).encD i x = blumEnc i (rabinBlumTrapdoor_domEquiv H i x)
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:1002	TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_eval	theorem	theorem rabinBlumTrapdoor_eval (H : ArithmeticFP) : (rabinBlumTrapdoor H).eval = rabinEval
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:968	TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_f	theorem	theorem rabinBlumTrapdoor_f (H : ArithmeticFP) (i : List Bool) (x : (rabinBlumTrapdoor H).D i) : (rabinBlumTrapdoor H).f i x = blumF i (rabinBlumTrapdoor_domEquiv H i x)
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:995	TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_gen	theorem	theorem rabinBlumTrapdoor_gen (H : ArithmeticFP) : (rabinBlumTrapdoor H).gen = blumGen H
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:1005	TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_inv	theorem	theorem rabinBlumTrapdoor_inv (H : ArithmeticFP) : (rabinBlumTrapdoor H).inv = blumInv H
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:988	TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_perm	theorem	theorem rabinBlumTrapdoor_perm (H : ArithmeticFP) (i : List Bool) (x : (rabinBlumTrapdoor H).D i) : (rabinBlumTrapdoor H).perm i x = (rabinBlumTrapdoor_domEquiv H i).symm (blumPermAt i (rabinBlumTrapdoor_domEquiv H i x))
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:998	TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_sample	theorem	theorem rabinBlumTrapdoor_sample (H : ArithmeticFP) : (rabinBlumTrapdoor H).sample = blumSampler H
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:541	TCSlib.Cryptography.Candidates.rabinCollection_decD	theorem	theorem rabinCollection_decD (H : ArithmeticFP) (i w : List Bool) : (rabinCollection H).decD i w = (rabinDec i w).map (rabinCollection_domEquiv H i).symm
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:516	TCSlib.Cryptography.Candidates.rabinCollection_domEquiv	def	def rabinCollection_domEquiv (H : ArithmeticFP) (i : List Bool) : (rabinCollection H).D i ≃ (ZMod (rabinMod i))ˣ
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:523	TCSlib.Cryptography.Candidates.rabinCollection_domEquiv_uprob	theorem	theorem rabinCollection_domEquiv_uprob (H : ArithmeticFP) (i : List Bool) (P : (ZMod (rabinMod i))ˣ → Prop) : uprob (fun x : (rabinCollection H).D i => P (rabinCollection_domEquiv H i x)) = uprob P
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:535	TCSlib.Cryptography.Candidates.rabinCollection_encD	theorem	theorem rabinCollection_encD (H : ArithmeticFP) (i : List Bool) (x : (rabinCollection H).D i) : (rabinCollection H).encD i x = rabinEnc i (rabinCollection_domEquiv H i x)
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:554	TCSlib.Cryptography.Candidates.rabinCollection_eval	theorem	theorem rabinCollection_eval (H : ArithmeticFP) : (rabinCollection H).eval = rabinEval
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:530	TCSlib.Cryptography.Candidates.rabinCollection_f	theorem	theorem rabinCollection_f (H : ArithmeticFP) (i : List Bool) (x : (rabinCollection H).D i) : (rabinCollection H).f i x = rabinF i (rabinCollection_domEquiv H i x)
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:547	TCSlib.Cryptography.Candidates.rabinCollection_gen	theorem	theorem rabinCollection_gen (H : ArithmeticFP) : (rabinCollection H).gen = oddGen H
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:550	TCSlib.Cryptography.Candidates.rabinCollection_sample	theorem	theorem rabinCollection_sample (H : ArithmeticFP) : (rabinCollection H).sample = rabinSampler H
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:296	TCSlib.Cryptography.Candidates.smallDistinctPrimes_p	theorem	theorem smallDistinctPrimes_p (m : ℕ) {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b) (ha8 : a < 8) (hb8 : b < 8) : (smallDistinctPrimes m ha hb hab ha8 hb8).p = a
ADDED	TCSlib/Cryptography/Candidates/Rabin.lean:302	TCSlib.Cryptography.Candidates.smallDistinctPrimes_q	theorem	theorem smallDistinctPrimes_q (m : ℕ) {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b) (ha8 : a < 8) (hb8 : b < 8) : (smallDistinctPrimes m ha hb hab ha8 hb8).q = b
ADDED	TCSlib/Cryptography/Foundations/Experiments.lean:98	TCSlib.Cryptography.acceptProb_def	theorem	theorem acceptProb_def (X : σ → γ) (D : γ → ρ → Bool) : acceptProb X D = uprob fun z : σ × ρ => D (X z.1) z.2 = true
ADDED	TCSlib/Cryptography/Foundations/Experiments.lean:102	TCSlib.Cryptography.distAdv_def	theorem	theorem distAdv_def (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) : distAdv X Y D = |acceptProb X D - acceptProb Y D|
ADDED	TCSlib/Cryptography/Foundations/Experiments.lean:88	TCSlib.Cryptography.invProb_def	theorem	theorem invProb_def (f : α → β) (A : β → ρ → α) : invProb f A = uprob fun z : α × ρ => f (A (f z.1) z.2) = f z.1
ADDED	TCSlib/Cryptography/Foundations/Experiments.lean:93	TCSlib.Cryptography.predProb_def	theorem	theorem predProb_def (f : α → β) (B : α → Bool) (A : β → ρ → Bool) : predProb f B A = uprob fun z : α × ρ => A (f z.1) z.2 = B z.1
ADDED	TCSlib/Cryptography/Foundations/Negligible.lean:62	TCSlib.Cryptography.negligible_iff	theorem	theorem negligible_iff (μ : ℕ → ℝ) : Negligible μ ↔ ∀ c : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, |μ n| < 1 / (n : ℝ) ^ c
ADDED	TCSlib/Cryptography/Foundations/Probability.lean:72	TCSlib.Cryptography.uexp_def	theorem	theorem uexp_def (f : α → ℝ) : uexp f = (∑ a, f a) / Fintype.card α
ADDED	TCSlib/Cryptography/Foundations/Probability.lean:64	TCSlib.Cryptography.uprob_def	theorem	theorem uprob_def (p : α → Prop) : uprob p = (Nat.card {a // p a} : ℝ) / Fintype.card α
ADDED	TCSlib/Cryptography/HardcoreBit/Basic.lean:177	TCSlib.Cryptography.HardcoreBit.pushesUniform_iff	theorem	theorem pushesUniform_iff (π : Ω → γ) : PushesUniform π ↔ ∀ F : γ → ℝ, uexp (fun ω => F (π ω)) = uexp F
ADDED	TCSlib/Cryptography/HardcoreBit/GoldreichLevin.lean:101	TCSlib.Cryptography.HardcoreBit.guessCoinsCongr	def	def guessCoinsCongr {ρ' : Type*} (k : ℕ) (e : ρ' ≃ ρ) : GuessCoins n k ρ' ≃ GuessCoins n k ρ
ADDED	TCSlib/Cryptography/HardcoreBit/GoldreichLevin.lean:108	TCSlib.Cryptography.HardcoreBit.guessCoinsCongr_apply	theorem	theorem guessCoinsCongr_apply {ρ' : Type*} (k : ℕ) (e : ρ' ≃ ρ) (c : GuessCoins n k ρ') : guessCoinsCongr k e c = (c.1, c.2.1, fun i L => e (c.2.2 i L))
ADDED	TCSlib/Cryptography/HardcoreBit/GoldreichLevin.lean:97	TCSlib.Cryptography.HardcoreBit.guessInverter_eq	theorem	theorem guessInverter_eq (A : β × (Fin n → Bool) → ρ → Bool) (k : ℕ) : guessInverter A k = glInverter (guessRecover A k)
ADDED	TCSlib/Cryptography/HardcoreBit/GoldreichLevin.lean:83	TCSlib.Cryptography.HardcoreBit.guessRecover_apply	theorem	theorem guessRecover_apply (A : β × (Fin n → Bool) → ρ → Bool) (k : ℕ) (y : β) (c : GuessCoins n k ρ) (i : Fin n) : guessRecover A k y c i = majority fun L : NESubset k => subsetSum L.1 c.2.1 + A (y, subsetSum L.1 c.1 + Pi.single i true) (c.2.2 i L)
ADDED	TCSlib/Cryptography/HardcoreBit/GoldreichLevin.lean:114	TCSlib.Cryptography.HardcoreBit.guessRecover_coinsCongr	theorem	theorem guessRecover_coinsCongr {ρ' : Type*} (A : β × (Fin n → Bool) → ρ → Bool) (A' : β × (Fin n → Bool) → ρ' → Bool) (e : ρ' ≃ ρ) (h : ∀ p c, A' p c = A p (e c)) (k : ℕ) (y : β) (c : GuessCoins n k ρ') : guessRecover A' k y c = guessRecover A k y (guessCoinsCongr k e c)
ADDED	TCSlib/Cryptography/HardcoreBit/InnerProduct.lean:119	TCSlib.Cryptography.HardcoreBit.glInverter_apply	theorem	theorem glInverter_apply (R : β → γ → Fin n → Bool) (y : β × (Fin n → Bool)) (c : γ) : glInverter R y c = (R y.1 c, y.2)
ADDED	TCSlib/Cryptography/HardcoreBit/InnerProduct.lean:105	TCSlib.Cryptography.HardcoreBit.glPad_apply	theorem	theorem glPad_apply (f : (Fin n → Bool) → β) (z : (Fin n → Bool) × (Fin n → Bool)) : glPad f z = (f z.1, z.2)
ADDED	TCSlib/Cryptography/HardcoreBit/InnerProduct.lean:217	TCSlib.Cryptography.HardcoreBit.perfectInverter_eq	theorem	theorem perfectInverter_eq (A : β × (Fin n → Bool) → ρ → Bool) : perfectInverter A = glInverter (perfectRecover A)
ADDED	TCSlib/Cryptography/HardcoreBit/PairwiseIndependence.lean:285	TCSlib.Cryptography.HardcoreBit.subsetSum_eq	theorem	theorem subsetSum_eq (L : Finset κ) (s : κ → G) : subsetSum L s = ∑ j ∈ L, s j
ADDED	TCSlib/Cryptography/HardcoreBit/ThreeQuarters.lean:75	TCSlib.Cryptography.HardcoreBit.majorityInverter_eq	theorem	theorem majorityInverter_eq (A : β × (Fin n → Bool) → ρ → Bool) (T : ℕ) : majorityInverter A T = glInverter (majorityRecover A T)
ADDED	TCSlib/Cryptography/NumberTheory/Primality.lean:693	TCSlib.Cryptography.NumberTheory.chunk_apply	theorem	theorem chunk_apply (T n : ℕ) (r : Fin (T * n) → Bool) (t : Fin T) (i : Fin n) : chunk T n r t i = r (finProdFinEquiv (t, i))
ADDED	TCSlib/Cryptography/NumberTheory/Primality.lean:667	TCSlib.Cryptography.NumberTheory.listToNat_eq	theorem	theorem listToNat_eq (w : List Bool) : listToNat w = w.foldl (fun a c => 2 * a + if c then 1 else 0) 0
ADDED	TCSlib/Cryptography/OneWayFunctions/Amplification.lean:79	TCSlib.Cryptography.OneWay.prodFun_apply	theorem	theorem prodFun_apply (f : α → β) (q : ℕ) (xs : Fin q → α) (i : Fin q) : prodFun f q xs i = f (xs i)
ADDED	TCSlib/Cryptography/OneWayFunctions/Amplification.lean:96	TCSlib.Cryptography.OneWay.yaoTry_eq	theorem	theorem yaoTry_eq (f : α → β) (B : (Fin q → β) → ρ → (Fin q → α)) (y : β) (c : Fin q × (Fin q → α) × ρ) : yaoTry f B y c = B (Function.update (prodFun f q c.2.1) c.1 y) c.2.2 c.1
ADDED	TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean:94	TCSlib.Cryptography.owpPredictor_apply	theorem	theorem owpPredictor_apply (D : α × β × Bool → ρ → Bool) (flip : Bool) (y : α × β) (c : Bool × ρ) : owpPredictor D flip y c = xor (if D (y.1, y.2, c.1) c.2 then c.1 else !c.1) flip
ADDED	TCSlib/Cryptography/Pseudorandom/Generators.lean:77	TCSlib.Cryptography.prgAdv_eq	theorem	theorem prgAdv_eq [Fintype γ] (G : σ → γ) (D : γ → ρ → Bool) : prgAdv G D = distAdv G (id : γ → γ) D
CHANGED	TCSlib/Cryptography/ZeroKnowledge/Commitment.lean:642->642	TCSlib.Cryptography.HardCore.bitHiding	theorem	theorem HardCore.bitHiding {P : PermFamily} {h : ∀ n, (Fin n → Bool) → Bool} (hh : HardCore P.toFunFamily h) : BitHiding P h	=>	theorem HardCore.bitHiding {P : PermFamily} {h : ∀ n, (Fin n → Bool) → Bool} (hh : P.HardCore h) : BitHiding P h
CHANGED	TCSlib/Cryptography/ZeroKnowledge/Commitment.lean:447->447	TCSlib.Cryptography.bitCom_false_eq_owpGenPRG	theorem	theorem bitCom_false_eq_owpGenPRG (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) (r : Fin n → Bool) (i : Fin (n + 1)) : bitCom (P.f n) (h n) false r i = (owpGenPRG P h).G n r i	=>	theorem bitCom_false_eq_owpGenPRG (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) (r : Fin n → Bool) (i : Fin (n + 1)) : bitCom (P.f n) (h n) false r i = owpGenPRG_outEquiv P h n ((owpGenPRG P h).G n r) i
CHANGED	TCSlib/Cryptography/ZeroKnowledge/Commitment.lean:898->899	TCSlib.Cryptography.exists_commitment_of_owp_hardCore	theorem	theorem exists_commitment_of_owp_hardCore (hex : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool), OneWayPermutation P ∧ HardCore P.toFunFamily h) : ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ	=>	theorem exists_commitment_of_owp_hardCore (hex : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool), OneWayPermutation P ∧ P.HardCore h) : ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ
CHANGED	TCSlib/Cryptography/ZeroKnowledge/Commitment.lean:889->890	TCSlib.Cryptography.owp_commitment	theorem	theorem owp_commitment (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (hP : OneWayPermutation P) (hh : HardCore P.toFunFamily h) : Commitment (owpComStr P h) owpComLen	=>	theorem owp_commitment (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (hP : OneWayPermutation P) (hh : P.HardCore h) : Commitment (owpComStr P h) owpComLen
ADDED	TCSlib/Cryptography/ZeroKnowledge/Defs.lean:166	TCSlib.Cryptography.ZK_iff	theorem	theorem ZK_iff (π : Protocol) (R : List Bool → List Bool → Prop) : ZK π R ↔ ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ x y z, R x y → z.length ≤ Lz.eval x.length → distAdv (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
ADDED	TCSlib/Cryptography/ZeroKnowledge/Encoding.lean:237	TCSlib.Cryptography.encColoring_eq	theorem	theorem encColoring_eq {n : ℕ} (c : Fin n → Fin 3) : encColoring c = List.ofFn fun k : Fin (n * 2) => if (finProdFinEquiv.symm k).2 = 0 then decide ((c (finProdFinEquiv.symm k).1).val / 2 = 1) else decide ((c (finProdFinEquiv.symm k).1).val % 2 = 1)
ADDED	TCSlib/Cryptography/ZeroKnowledge/Encoding.lean:244	TCSlib.Cryptography.getD_encColoring	theorem	theorem getD_encColoring {n : ℕ} (c : Fin n → Fin 3) (i : Fin n) (b : Fin 2) : (encColoring c).getD (finProdFinEquiv (i, b)) false = if b = 0 then decide ((c i).val / 2 = 1) else decide ((c i).val % 2 = 1)
ADDED	TCSlib/Cryptography/ZeroKnowledge/Encoding.lean:257	TCSlib.Cryptography.getD_encColoring_two_mul	theorem	theorem getD_encColoring_two_mul {n : ℕ} (c : Fin n → Fin 3) (i : Fin n) : (encColoring c).getD (2 * i) false = decide ((c i).val / 2 = 1)
ADDED	TCSlib/Cryptography/ZeroKnowledge/Encoding.lean:264	TCSlib.Cryptography.getD_encColoring_two_mul_add_one	theorem	theorem getD_encColoring_two_mul_add_one {n : ℕ} (c : Fin n → Fin 3) (i : Fin n) : (encColoring c).getD (2 * i + 1) false = decide ((c i).val % 2 = 1)
ADDED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean:532	TCSlib.Cryptography.giProtocol_eq	theorem	theorem giProtocol_eq : giProtocol = { P := giProver, V := giVerifier, rounds := .const 3, verifierFirst := false }
ADDED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean:501	TCSlib.Cryptography.giProver_coins	theorem	theorem giProver_coins : giProver.coins = .normal 1 2
ADDED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:593	TCSlib.Cryptography.GI.giProtocolRep_V_coinLen	theorem	theorem giProtocolRep_V_coinLen (N : ℕ) : giProtocolRep.V.coinLen N = N
ADDED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:587	TCSlib.Cryptography.GI.giProtocol_V_coinLen	theorem	theorem giProtocol_V_coinLen (N : ℕ) : giProtocol.V.coinLen N = 1
ADDED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:579	TCSlib.Cryptography.GI.gniProtocolRep_V_coinLen	theorem	theorem gniProtocolRep_V_coinLen (N : ℕ) : gniProtocolRep.V.coinLen N = N * (1 + 1 * (N + 1) ^ 2)
ADDED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:572	TCSlib.Cryptography.GI.gniProtocol_V_coinLen	theorem	theorem gniProtocol_V_coinLen (N : ℕ) : gniProtocol.V.coinLen N = 1 + 1 * (N + 1) ^ 2
CHANGED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean:229->233	TCSlib.Cryptography.GI.giBitEquiv	def	def giBitEquiv (N : ℕ) : Bool ≃ giProtocol.V.Coins N	=>	noncomputable def giBitEquiv (N : ℕ) : Bool ≃ giProtocol.V.Coins N
CHANGED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean:237->247	TCSlib.Cryptography.GI.giCoinEquiv	def	def giCoinEquiv (P' : Strategy) (x : List Bool) : Bool × P'.Coins x.length ≃ giProtocol.ExecCoins P' x	=>	noncomputable def giCoinEquiv (P' : Strategy) (x : List Bool) : Bool × P'.Coins x.length ≃ giProtocol.ExecCoins P' x
CHANGED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean:101->101	TCSlib.Cryptography.GI.vTapeSplit	def	def vTapeSplit (N : ℕ) : Bool × (Fin (1 * (N + 1) ^ 2) → Bool) ≃ gniProtocol.V.Coins N	=>	noncomputable def vTapeSplit (N : ℕ) : Bool × (Fin (1 * (N + 1) ^ 2) → Bool) ≃ gniProtocol.V.Coins N
CHANGED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:268->268	TCSlib.Cryptography.GI.gniTapes	def	def gniTapes (N : ℕ) : (Fin N → Bool) × (Fin N → (Fin (1 * (N + 1) ^ 2) → Bool)) ≃ gniProtocolRep.V.Coins N	=>	noncomputable def gniTapes (N : ℕ) : (Fin N → Bool) × (Fin N → (Fin (1 * (N + 1) ^ 2) → Bool)) ≃ gniProtocolRep.V.Coins N
CHANGED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:274->276	TCSlib.Cryptography.GI.gniTapes_apply	theorem	theorem gniTapes_apply (N : ℕ) (b : Fin N → Bool) (ts : Fin N → (Fin (1 * (N + 1) ^ 2) → Bool)) : gniTapes N (b, ts) = blocksEquiv N (1 + 1 * (N + 1) ^ 2) (fun j => tapeSplit _ (b j, ts j))	=>	theorem gniTapes_apply (N : ℕ) (b : Fin N → Bool) (ts : Fin N → (Fin (1 * (N + 1) ^ 2) → Bool)) : List.ofFn (gniTapes N (b, ts)) = List.ofFn (blocksEquiv N (1 + 1 * (N + 1) ^ 2) (fun j => tapeSplit _ (b j, ts j)))
CHANGED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean:382->382	TCSlib.Cryptography.GI.giRepCoins	def	def giRepCoins (P' : Strategy) (x : List Bool) : (Fin x.length → Bool) × P'.Coins x.length ≃ giProtocolRep.ExecCoins P' x	=>	noncomputable def giRepCoins (P' : Strategy) (x : List Bool) : (Fin x.length → Bool) × P'.Coins x.length ≃ giProtocolRep.ExecCoins P' x
CHANGED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:364->370	TCSlib.Cryptography.GIZK.sim_ofFn_eq	theorem	theorem sim_ofFn_eq (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (z : List Bool) {M : ℕ} (hn : n ≤ M) (r : Fin (M * blockLen V' (encInstance G₀ G₁).length) → Bool) : sim V' (encInstance G₀ G₁) z (List.ofFn r) = (Option.map (encView V' (encInstance G₀ G₁) z) (simTrunc G₀ G₁ (vstar V' (encInstance G₀ G₁) z) n fun t => ((samplePerm n (List.ofFn (readBlocks _ _ M n hn r t).1.1), (readBlocks _ _ M n hn r t).1.2), (readBlocks _ _ M n hn r t).2))).getD []	=>	theorem sim_ofFn_eq (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (z : List Bool) {M : ℕ} (hn : n ≤ M) (r : Fin (M * blockLen V' (encInstance G₀ G₁).length) → Bool) : sim V' (encInstance G₀ G₁) z (List.ofFn r) = (Option.map (encView V' (encInstance G₀ G₁) z) (simTrunc G₀ G₁ (vstar V' (encInstance G₀ G₁) z) n fun t => ((samplePerm n (List.ofFn (readBlocks _ _ M n hn (blockTapeEquiv V' _ M r) t).1.1), (readBlocks _ _ M n hn (blockTapeEquiv V' _ M r) t).1.2), (readBlocks _ _ M n hn (blockTapeEquiv V' _ M r) t).2))).getD []
CHANGED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:441->458	TCSlib.Cryptography.GIZK.statClose_real_ideal	theorem	theorem statClose_real_ideal (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (z : List Bool) : StatClose (fun r : (giProtocol.withV V').ExecCoins giProtocol.P (encInstance G₀ G₁) => ((giProtocol.withV V').viewV (encInstance G₀ G₁) (encPerm σ) z r).encode) (fun w : Equiv.Perm (Fin n) × V'.Coins (encInstance G₀ G₁).length => encView V' (encInstance G₀ G₁) z (realView G₀ σ (vstar V' (encInstance G₀ G₁) z) w)) (permFailBound n + 0)	=>	theorem statClose_real_ideal (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (z : List Bool) : StatClose (fun r : (giProtocol.withV V').ExecCoins (giProtocol.withV V').P (encInstance G₀ G₁) => ((giProtocol.withV V').viewV (encInstance G₀ G₁) (encPerm σ) z r).encode) (fun w : Equiv.Perm (Fin n) × V'.Coins (encInstance G₀ G₁).length => encView V' (encInstance G₀ G₁) z (realView G₀ σ (vstar V' (encInstance G₀ G₁) z) w)) (permFailBound n + 0)
CHANGED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:505->525	TCSlib.Cryptography.GIZK.statClose_real_sim	theorem	theorem statClose_real_sim (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (z : List Bool) (hclose : StatClose (simTrunc G₀ G₁ (vstar V' (encInstance G₀ G₁) z) n) (fun w => some (realView G₀ σ (vstar V' (encInstance G₀ G₁) z) w)) ((2 : ℝ)⁻¹ ^ n)) (m : ℕ) (hm : m = (encInstance G₀ G₁).length * blockLen V' (encInstance G₀ G₁).length) : StatClose (fun r : (giProtocol.withV V').ExecCoins giProtocol.P (encInstance G₀ G₁) => ((giProtocol.withV V').viewV (encInstance G₀ G₁) (encPerm σ) z r).encode) (fun r : Fin m → Bool => sim V' (encInstance G₀ G₁) z (List.ofFn r)) ((2 : ℝ)⁻¹ ^ n + ((n : ℝ) + 1) * permFailBound n)	=>	theorem statClose_real_sim (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (z : List Bool) (hclose : StatClose (simTrunc G₀ G₁ (vstar V' (encInstance G₀ G₁) z) n) (fun w => some (realView G₀ σ (vstar V' (encInstance G₀ G₁) z) w)) ((2 : ℝ)⁻¹ ^ n)) (m : ℕ) (hm : m = (encInstance G₀ G₁).length * blockLen V' (encInstance G₀ G₁).length) : StatClose (fun r : (giProtocol.withV V').ExecCoins (giProtocol.withV V').P (encInstance G₀ G₁) => ((giProtocol.withV V').viewV (encInstance G₀ G₁) (encPerm σ) z r).encode) (fun r : Fin m → Bool => sim V' (encInstance G₀ G₁) z (List.ofFn r)) ((2 : ℝ)⁻¹ ^ n + ((n : ℝ) + 1) * permFailBound n)
CHANGED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:414->426	TCSlib.Cryptography.GIZK.viewV_encode	theorem	theorem viewV_encode (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (z : List Bool) (r : (giProtocol.withV V').ExecCoins giProtocol.P (encInstance G₀ G₁)) : ((giProtocol.withV V').viewV (encInstance G₀ G₁) (encPerm σ) z r).encode = encView V' (encInstance G₀ G₁) z (realView G₀ σ (vstar V' (encInstance G₀ G₁) z) (samplePerm n (List.ofFn r.1), r.2))	=>	theorem viewV_encode (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (z : List Bool) (r : (giProtocol.withV V').ExecCoins (giProtocol.withV V').P (encInstance G₀ G₁)) : ((giProtocol.withV V').viewV (encInstance G₀ G₁) (encPerm σ) z r).encode = encView V' (encInstance G₀ G₁) z (realView G₀ σ (vstar V' (encInstance G₀ G₁) z) (samplePerm n (List.ofFn r.1), giProtocol.withV_vCoinsEquiv V' _ r.2))
ADDED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean:72	TCSlib.Cryptography.GIZK.blockLen_eq	theorem	theorem blockLen_eq (V' : Strategy) (N : ℕ) : blockLen V' N = 1 + (N + 1) ^ 2 + V'.coinLen N
ADDED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean:77	TCSlib.Cryptography.GIZK.blockTapeEquiv	def	def blockTapeEquiv (V' : Strategy) (N M : ℕ) : (Fin (M * blockLen V' N) → Bool) ≃ (Fin (M * (1 + (N + 1) ^ 2 + V'.coinLen N)) → Bool)
ADDED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean:82	TCSlib.Cryptography.GIZK.blockTapeEquiv_ofFn	theorem	theorem blockTapeEquiv_ofFn (V' : Strategy) (N M : ℕ) (r : Fin (M * blockLen V' N) → Bool) : List.ofFn (blockTapeEquiv V' N M r) = List.ofFn r
ADDED	TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean:119	TCSlib.Cryptography.GIZK.sim_eq	theorem	theorem sim_eq (V' : Strategy) (x z r : List Bool) : sim V' x z r = ((List.range (instanceVertexCount x)).findSome? fun t => attemptStr V' x z (coinSlice (blockLen V' x.length) t r)).getD []
ADDED	TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:422	TCSlib.Cryptography.Protocol.outV_eq	theorem	theorem outV_eq (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.ExecCoins P' x) : π.outV P' x y z r = π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2
ADDED	TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:403	TCSlib.Cryptography.Protocol.transcriptWith_eq	theorem	theorem transcriptWith_eq (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.ExecCoins P' x) : π.transcriptWith P' x y z r = exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)
ADDED	TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:436	TCSlib.Cryptography.Protocol.viewV_withV	theorem	theorem viewV_withV (π : Protocol) (V' : Strategy) (x y z : List Bool) (r : (π.withV V').ExecCoins (π.withV V').P x) : (π.withV V').viewV x y z r = ⟨x, z, List.ofFn r.2, (exec π.P V' π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)).2⟩
ADDED	TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:373	TCSlib.Cryptography.Protocol.withV_vCoinsEquiv	def	def withV_vCoinsEquiv (π : Protocol) (V' : Strategy) (n : ℕ) : (π.withV V').V.Coins n ≃ V'.Coins n
ADDED	TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:378	TCSlib.Cryptography.Protocol.withV_vCoinsEquiv_ofFn	theorem	theorem withV_vCoinsEquiv_ofFn (π : Protocol) (V' : Strategy) (n : ℕ) (r : (π.withV V').V.Coins n) : List.ofFn (π.withV_vCoinsEquiv V' n r) = List.ofFn r
ADDED	TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:126	TCSlib.Cryptography.Strategy.coinLen_eq	theorem	theorem coinLen_eq (S : Strategy) (n : ℕ) : S.coinLen n = S.coins.eval n
ADDED	TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:181	TCSlib.Cryptography.Strategy.efficient_iff	theorem	theorem efficient_iff (S : Strategy) : S.Efficient ↔ ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins ∧ ∀ x z r hist, S.next x z r hist = (ofNUPPT A).next x z r hist
ADDED	TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:294	TCSlib.Cryptography.View.encode_mk	theorem	theorem View.encode_mk (x z r : List Bool) (received : List (List Bool)) : View.encode ⟨x, z, r, received⟩ = pairEncode (pairEncode x z) (pairEncode r (Strategy.encodeMsgs received))
CHANGED	TCSlib/Cryptography/ZeroKnowledge/NP.lean:754->756	TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp	theorem	theorem zk_proof_of_mem_NP_of_owp (h3 : LevinNPHard L3COL R3COL) (how : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool), OneWayPermutation P ∧ HardCore P.toFunFamily h) {L : Language Bool} (hL : L ∈ NP) : ∃ R : List Bool → List Bool → Prop, WitnessRelation L R ∧ (∃ π : Protocol, EfficientProverProof π L R) ∧ ∃ (π : Protocol) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ ZK π R ∧ EfficientProverProofErr π L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)	=>	theorem zk_proof_of_mem_NP_of_owp (h3 : LevinNPHard L3COL R3COL) (how : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool), OneWayPermutation P ∧ P.HardCore h) {L : Language Bool} (hL : L ∈ NP) : ∃ R : List Bool → List Bool → Prop, WitnessRelation L R ∧ (∃ π : Protocol, EfficientProverProof π L R) ∧ ∃ (π : Protocol) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ ZK π R ∧ EfficientProverProofErr π L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)
CHANGED	TCSlib/Cryptography/ZeroKnowledge/NP.lean:613->615	TCSlib.Cryptography.zk_proof_of_owp_levinReduction	theorem	theorem zk_proof_of_owp_levinReduction (how : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool), OneWayPermutation P ∧ HardCore P.toFunFamily h) {L : Language Bool} {R : List Bool → List Bool → Prop} {f : List Bool → List Bool} {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L3COL R R3COL f w p) (hLR : ∀ x ∈ L, ∃ y, R x y) : (∃ π : Protocol, EfficientProverProof π L R) ∧ ∃ π : Protocol, ZK π R ∧ EfficientProverProofErr π L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)	=>	theorem zk_proof_of_owp_levinReduction (how : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool), OneWayPermutation P ∧ P.HardCore h) {L : Language Bool} {R : List Bool → List Bool → Prop} {f : List Bool → List Bool} {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L3COL R R3COL f w p) (hLR : ∀ x ∈ L, ∃ y, R x y) : (∃ π : Protocol, EfficientProverProof π L R) ∧ ∃ π : Protocol, ZK π R ∧ EfficientProverProofErr π L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean:95	TCSlib.Cryptography.ProperColoring.ne	theorem	theorem ProperColoring.ne {n : ℕ} {G : Graph n} {c : Fin n → Fin 3} (h : ProperColoring G c) {u v : Fin n} (huv : G u v = true) : c u ≠ c v
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean:90	TCSlib.Cryptography.ProperColoring_iff	theorem	theorem ProperColoring_iff {n : ℕ} (G : Graph n) (c : Fin n → Fin 3) : ProperColoring G c ↔ ∀ u v, G u v = true → c u ≠ c v
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean:132	TCSlib.Cryptography.R3COL_iff	theorem	theorem R3COL_iff (x y : List Bool) : R3COL x y ↔ ∃ (n : ℕ) (G : Graph n) (c : Fin n → Fin 3), x = encGraph G ∧ y = encColoring c ∧ ProperColoring G c
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean:347	TCSlib.Cryptography.edgeIdxOfMsg_eq	theorem	theorem edgeIdxOfMsg_eq (m : ℕ) (w : List Bool) : edgeIdxOfMsg m w = w.length % m
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean:312	TCSlib.Cryptography.sampleIdx_eq_rejectionSample	theorem	theorem sampleIdx_eq_rejectionSample (m k T : ℕ) (r : List Bool) : sampleIdx m k T r = rejectionSample m k T fun t j => r.getD (t * k + j) false
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean:390	TCSlib.Cryptography.sampleIdx_ofFn_eq_rejectionSample	theorem	theorem sampleIdx_ofFn_eq_rejectionSample (m k T : ℕ) (r : Fin (T * k) → Bool) : sampleIdx m k T (List.ofFn r) = rejectionSample m k T fun t j => r (finProdFinEquiv (t, j))
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:494	TCSlib.Cryptography.colCoinSlice_eq	theorem	theorem colCoinSlice_eq (c t : ℕ) (r : List Bool) : colCoinSlice c t r = (r.drop (t * c)).take c
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:128	TCSlib.Cryptography.colCommit_eq	theorem	theorem colCommit_eq (Com : List Bool → List Bool) (n ℓn : ℕ) (c' : Fin n → Fin 3) (r : Fin n → Fin ℓn → Bool) : colCommit Com n ℓn c' r = multiCom Com (fun i => padColor n (c' i)) r
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:503	TCSlib.Cryptography.colIterations_eq	theorem	theorem colIterations_eq (x : List Bool) : colIterations x = (decGraph x).1 * edgeCount (decGraph x).2
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:140	TCSlib.Cryptography.colOpen_eq	theorem	theorem colOpen_eq {n ℓn : ℕ} (c' : Fin n → Fin 3) (r : Fin n → Fin ℓn → Bool) (p : Fin n × Fin n) : colOpen c' r p = pairEncode (pairEncode (encColor (c' p.1)) (List.ofFn (r p.1))) (pairEncode (encColor (c' p.2)) (List.ofFn (r p.2)))
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:472	TCSlib.Cryptography.colProtocol_P	theorem	theorem colProtocol_P (Com : List Bool → List Bool) (ℓ : PolyExpr) : (colProtocol Com ℓ).P = colProver Com ℓ
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:476	TCSlib.Cryptography.colProtocol_V	theorem	theorem colProtocol_V (Com : List Bool → List Bool) (ℓ : PolyExpr) : (colProtocol Com ℓ).V = colVerifier Com ℓ
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:480	TCSlib.Cryptography.colProtocol_rounds	theorem	theorem colProtocol_rounds (Com : List Bool → List Bool) (ℓ : PolyExpr) : (colProtocol Com ℓ).rounds = .const 3
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:484	TCSlib.Cryptography.colProtocol_verifierFirst	theorem	theorem colProtocol_verifierFirst (Com : List Bool → List Bool) (ℓ : PolyExpr) : (colProtocol Com ℓ).verifierFirst = false
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:439	TCSlib.Cryptography.colProver_coins	theorem	theorem colProver_coins (Com : List Bool → List Bool) (ℓ : PolyExpr) : (colProver Com ℓ).coins = .add (.mul (.const 3) .var) (.mul .var ℓ)
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:719	TCSlib.Cryptography.colProver_next_cons	theorem	theorem colProver_next_cons (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool} {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (hm : 0 < edgeCount G) (y r w : List Bool) (h : List (List Bool)) : (colProver Com ℓ).next x y r (w :: h) = colOpen (fun i => samplePerm3 x.length (r.take (3 * x.length)) (decColoring n y i)) (fun (i : Fin n) (j : Fin (ℓ.eval n)) => r.getD (3 * x.length + i * ℓ.eval n + j) false) (edgeOf G ⟨edgeIdxOfMsg (edgeCount G) w % edgeCount G, Nat.mod_lt _ hm⟩)
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:729	TCSlib.Cryptography.colProver_next_cons_of_edgeCount_eq_zero	theorem	theorem colProver_next_cons_of_edgeCount_eq_zero (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool} {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (hm : edgeCount G = 0) (y r w : List Bool) (h : List (List Bool)) : (colProver Com ℓ).next x y r (w :: h) = []
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:710	TCSlib.Cryptography.colProver_next_nil	theorem	theorem colProver_next_nil (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool} {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (y r : List Bool) : (colProver Com ℓ).next x y r [] = colCommit Com n (ℓ.eval n) (fun i => samplePerm3 x.length (r.take (3 * x.length)) (decColoring n y i)) (fun i j => r.getD (3 * x.length + i * ℓ.eval n + j) false)
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:106	TCSlib.Cryptography.msgAt_eq	theorem	theorem msgAt_eq (w : List Bool) (i : ℕ) : msgAt w i = pairFstD (pairSndD^[i] w)
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean:441	TCSlib.Cryptography.ColSimLemmas.hybGen_eq	theorem	theorem hybGen_eq (H Wa : W → Option α) {N : ℕ} (k : Fin N) (A : W → Option α) (D : Option α → ρ' → Bool) (z : (Fin N → W) × ρ') : hybGen H Wa k A D z = D ((List.finRange N).findSome? fun t : Fin N => if (t : ℕ) < k then H (z.1 t) else if t = k then A (z.1 t) else Wa (z.1 t)) z.2
ADDED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean:427	TCSlib.Cryptography.ColSimLemmas.hybStd_eq	theorem	theorem hybStd_eq (H Wa : W → Option α) (N k : ℕ) (w : Fin N → W) : hybStd H Wa N k w = (List.finRange N).findSome? fun t : Fin N => if (t : ℕ) < k then H (w t) else Wa (w t)
ADDED	TCSlib/InformationTheory/StatisticalDistance.lean:49	TCSlib.InformationTheory.statDist_eq	theorem	theorem statDist_eq (p q : FinDist α) : statDist p q = (1 / 2) * ∑ a, |p a - q a|

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/replay-head.log =====

HEAD eb99dd7bb2d8a270b2ce17a3cf3e1487a65ad0ee
MODULE TCSlib/Cryptography/Foundations/Experiments rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/OneWayFunctions/Basic rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/Asymptotic/Sampling rc=0 errors=0 sorry=0 secs=6
MODULE TCSlib/Cryptography/Asymptotic/SamplingFinDist rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/Asymptotic/Permutations rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/Asymptotic/Adversary rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/Pseudorandom/Indistinguishability rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/Asymptotic/EnsemblesLemmas rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/Pseudorandom/Generators rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/Asymptotic/Ensembles rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/OneWayFunctions/Amplification rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 errors=0 sorry=0 secs=61
MODULE TCSlib/Cryptography/Asymptotic/OneWay rc=0 errors=0 sorry=0 secs=8
MODULE TCSlib/Cryptography/Asymptotic/CollectionsHelpers rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/Asymptotic/Collections rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/Asymptotic/UniversalLemmas rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/Asymptotic/UniversalPadding rc=0 errors=0 sorry=1 secs=4
MODULE TCSlib/Cryptography/OneWayFunctions/OutputLength rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/Asymptotic/Universal rc=0 errors=0 sorry=1 secs=8
MODULE TCSlib/Cryptography/Asymptotic/Pseudorandom rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/Asymptotic/NextBit rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/HardcoreBit/InnerProduct rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/HardcoreBit/GoldreichLevin rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/Asymptotic/GoldreichLevinDomain rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/HardcoreBit/ThreeQuarters rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/Asymptotic/HardCoreLemmas rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/Asymptotic/HardCoreLoops rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/Asymptotic/HardCoreGL rc=0 errors=0 sorry=0 secs=8
MODULE TCSlib/Cryptography/Asymptotic/HardCoreGLColl rc=0 errors=0 sorry=0 secs=6
MODULE TCSlib/Cryptography/Asymptotic/HardCoreCollection rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/Asymptotic/HardCoreGLFamily rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/Asymptotic/HardCore rc=0 errors=0 sorry=0 secs=5
MODULE TCSlib/Cryptography/Asymptotic/HardCoreClaims rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/Asymptotic/HardCorePermutation rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/Asymptotic/Encryption rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/Pseudorandom/Functions/LazySampling rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/Pseudorandom/Functions/Defs rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/Pseudorandom/Functions/GGM rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/Asymptotic/PRFLemmas rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/Asymptotic/GGMReduction rc=0 errors=0 sorry=0 secs=36
MODULE TCSlib/Cryptography/Asymptotic/GGMReductionEval rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/Asymptotic/PRF rc=0 errors=0 sorry=0 secs=5
MODULE TCSlib/Cryptography/Asymptotic/MultiMessageLemmas rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/Asymptotic/MultiMessage rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/Asymptotic/BlockEncryptor rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/Asymptotic/PublicKeyLemmas rc=0 errors=0 sorry=0 secs=61
MODULE TCSlib/Cryptography/Asymptotic/PublicKey rc=0 errors=0 sorry=0 secs=19
MODULE TCSlib/Cryptography/Asymptotic rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/NumberTheory/Chebyshev rc=0 errors=0 sorry=0 secs=5
MODULE TCSlib/Cryptography/NumberTheory/Primality rc=0 errors=0 sorry=0 secs=6
MODULE TCSlib/Cryptography/Candidates/Arithmetic rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/Candidates/Concrete rc=0 errors=0 sorry=1 secs=4
MODULE TCSlib/Cryptography/Candidates/Factoring rc=0 errors=0 sorry=10 secs=3
MODULE TCSlib/Cryptography/Candidates/RSA rc=0 errors=0 sorry=10 secs=7
MODULE TCSlib/Cryptography/NumberTheory/QuadraticResidues rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/Candidates/Rabin rc=0 errors=0 sorry=19 secs=6
MODULE TCSlib/Cryptography/Candidates/DiscreteLog rc=0 errors=0 sorry=6 secs=4
MODULE TCSlib/Cryptography/Candidates/DiscreteLogHardcore rc=0 errors=0 sorry=7 secs=4
MODULE TCSlib/Cryptography/Candidates/ElGamal rc=0 errors=0 sorry=7 secs=3
MODULE TCSlib/Cryptography/Candidates rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/Foundations rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/HardcoreBit/NoFixedBit rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/HardcoreBit rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/NumberTheory rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/OneWayFunctions/Robustness rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/OneWayFunctions/Brittleness rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/OneWayFunctions rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/Pseudorandom/Functions rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/Pseudorandom rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/ZeroKnowledge/EncodingPermutations rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/ZeroKnowledge/Encoding rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 errors=0 sorry=0 secs=5
MODULE TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK rc=0 errors=0 sorry=0 secs=5
MODULE TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/ZeroKnowledge/Commitment rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties rc=0 errors=0 sorry=0 secs=4
MODULE TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol rc=0 errors=0 sorry=2 secs=5
MODULE TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 errors=0 sorry=1 secs=4
MODULE TCSlib/Cryptography/ZeroKnowledge/ThreeColoring rc=0 errors=0 sorry=0 secs=2
MODULE TCSlib/Cryptography/ZeroKnowledge/NPLemmas rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/ZeroKnowledge/NP rc=0 errors=0 sorry=0 secs=10
MODULE TCSlib/Cryptography/ZeroKnowledge/Encryption rc=0 errors=0 sorry=0 secs=3
MODULE TCSlib/Cryptography/ZeroKnowledge rc=0 errors=0 sorry=0 secs=2
MODULE audits/pass-shelat/Checks rc=0 errors=0 sorry=0 secs=129
DONE

## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/style-lint.log =====


0 findings in 3 files




## ===== briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r3/check8b-diff.log =====


