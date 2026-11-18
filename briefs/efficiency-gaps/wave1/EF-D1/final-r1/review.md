# EF-D1 `ef-d1-lattice-families` · final r1 · phase-1 (static) maintainer review

**Verdict (with phase 2): ACCEPT WITH LANDING EDITS.** There is no blocker and no major.

The delivery adds `LWE.EfficientFamily` and `SIS.EfficientFamily` beside the raw families:
- each has a uniform parameter map in the `∃ f, PolyTimeComputable f ∧ …` form;
- the LWE noise sampler is in the `CoinSampling.SamplesEfficiently` form.

It also adds:
- the schedule theorems for both families;
- the bit-seed noise constructors;
- a polynomial-time core for `centeredNoise`;
- one non-vacuity instance of each structure, with no hardness claim.

`DLWEAssumption` and `SISAssumption` stay on the raw families, and `LWE.lean` is not edited.

Every integrity, reproduction, scope, statement, duplication, admission, axiom and seal check passes. I
recounted the worker's evidence from the raw files and bound it to the reproduced head.

**Two things need Seyoon before the PR leaves draft:**
- **EF-D1-R1**, the `CenteredSampleEq` question. It is not decided here.
- The `LWE.lean` import, a landing edit that this PR cannot carry (see *Landing*).

**Findings:**
- **Minors:** EFD1-F01 to EFD1-F05.
- **Information:** EFD1-I1 to EFD1-I4.

Phase 2 (`phase2.md`) replayed the delivery on the merge of `iO/phase-a-base` with the records tip:
- 20/20 modules rc 0, 0 errors, 0 `sorry`;
- standard axioms;
- canonical coe-A seal 0 errors;
- lint unchanged.

## What was reviewed

- **Delivery.** `inbox/fills/ef-d1-lattice-families/` on `exchange/pass-shelat-ch5-8`, at commit
  `9ad02e0dd1845b7fbb8b0ad127cb7b588879f610` ("fill ef-d1-lattice-families: final").
  - **The commit.** Its parent is `9a5cc15a`, it is unsigned (0 `gpgsig`), and it touches 270
    paths, all under the unit's folder.
  - **The path is unchanged at the exchange tip.** At the time of review the tip was `0c2ede1e`.
  - **The tree.** I extracted it with `git archive` into a fresh directory. It has 448 files:
    - `REPORT.md` (285 lines);
    - 4 patches with `COMMITS.tsv`;
    - `src/` (3 files);
    - `evidence/`.
  - **Manifests.** The top-level `SHA256SUMS` is `a4ea8953…`; `evidence/SHA256SUMS` is `67623e4f…`.
- **Contract.** The brief and the records it names:
  - `briefs/efficiency-gaps/wave1/EF-D1/brief.md`, `COMMON.md`, `rulings.md` and `README.md` at
    the records pin `54dcb3021a389831e7f94c3f82616cb7594fa574`. Between the pin and the tip
    `64d51439`, the brief, `COMMON.md` and `rulings.md` are unchanged. `README.md` and the
    dispatch prompt changed only in their pin and EF-D4 lines.
  - Handoff §2 rules 15 and 16.
- **Background.**
  - Decision-log rows 901 (checkpoint 1, the advance E-SCOPE) and 905.
  - The precedent reviews `briefs/pairings/fills/bb1-sim/fill-final-r1/` and
    `briefs/lattice-gsw/phase6/fills-final-r1/`.
- **Base.** `iO/phase-a-base` = `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`. It contains #374,
  #378, #384 (the contract `8e01b720`) and #380, all still open.

## Checks

| Check | Result |
|---|---|
| **Integrity** | **PASS.**<br>• Both manifests pass `sha256sum -c`.<br>• The delivered paths equal each manifest's paths exactly: nothing missing, nothing extra, no leading `./`, and neither manifest lists itself. |
| **Patches (C13)** | **PASS: 4/4 hashes reproduced.**<br>• Method: `git am` at the base in a sparse detached scratch worktree, with signing off and the committer name, e-mail and date per row of `COMMITS.tsv`.<br>• Hashes: `583c19f9`, `d01d3f41`, `dc2fb629`, `876b1cc00e6e54265f2cd1d97de985141b99c2e2` (= REPORT's head).<br>• No commit has a `gpgsig`.<br>• `src/` equals the head byte for byte, 3 of 3 files (`114f5112…`, `e9f7d368…`, `18c09d86…`).<br>• **Against checkpoint 1:** commits 1–2 are checkpoint 1's own (`d01d3f41` was the checkpoint head); 3–4 are new. |
| **Scope** | **PASS.** `git diff --stat 5ed465f6 876b1cc0` lists exactly the brief's three files:<br>• `LWE/Efficient.lean` +771 (new);<br>• `SIS/Efficient.lean` +308 (new);<br>• `SIS.lean` +2.<br>**`LWE.lean` is not edited.** The `SIS.lean` change is one `import` and one `## Contents` line, nothing else. |
| **Disjointness** | **PASS.**<br>• The two new files and `SIS.lean` are in no open PR (#359, #374, #378, #380, #382–#386 checked).<br>• They are not changed on `cleanup/stage2-s2a`.<br>• The SR1 target `LWE/BitNoise.lean` is in neither `scope.tsv` nor `s2a-items.tsv`, is unchanged on `cleanup/stage2-s2a` and is in no open PR. |
| **decls2 (C3)** | **PASS.**<br>• Pinned `decls2.py` (`fa81981a`), run by me on the reproduced head against the base.<br>• **94 ADDED, 0 CHANGED, 0 REMOVED**; the facade has no declarations.<br>• My output is byte-identical to the delivered `C3-decls2.tsv`. |
| **Clashes (C10)** | **PASS.**<br>• I grepped all **283 remote heads** (`git ls-remote` at review time; the 4 heads that had moved were fetched and grepped) for the 16 most distinctive new names (`EfficientFamily`, `noiseWord`, `seedModulusWord`, `centeredCore`, `signedDiff`, `onesCount`, `dyadicScheduleFamily`, `CenteredSampleEq`, `drawSamplable_restrict`, …): **0 hits** outside the delivery.<br>• A positive control (`bitNoise_Coins`, `samplesEfficiently_residue`) is hit on `iO/phase-a-base` and the tip.<br>• The worker's short-name list (`dyadicFamily`, `dyadicParameters`, `encode*`) is right: they live in other namespaces, and the only downstream modules are `SIS.lean` and the root. |
| **Admissions (C4)** | **PASS.** 0 `sorry`, `admit`, `native_decide`, `axiom` and `opaque` tokens in the 3 files. No existing file's code changed. |
| **Hygiene** | **PASS.**<br>• Sizes: 771 and 308 lines, at most 99 characters wide (`SIS.lean` 30 lines, 91 wide).<br>• No `@[simp]`, no new `attribute`.<br>• Mathlib-style headers with the repository copyright, `relaxedAutoImplicit false` and `autoImplicit false`.<br>• `maxHeartbeats 0` is the house form, as in `SIS.lean` and `BitNoise.lean`.<br>• Every public declaration has a docstring with its formula.<br>• Every proof of 15 or more lines has a `**Proof sketch.**`.<br>• Every definition has its `_eq`/`_iff` or projection readers. |
| **Citations** | [Pei16] Definitions 4.1.1, 4.2.1 and 4.2.3 and [PS10] Definitions 23.4 and 26.8 occur in the ingested `peikert2016-lattice-survey.md` and `pass-shelat-2010-ch2.raw.md`. Glue notes are present. Two wording points are **F04**. |

## Statements versus the brief

Every target of the brief maps to a declaration (REPORT §3). I checked the map against the source.

The six disclosed statement changes are:

1. **The noise sampler reads its own word `noiseInput κ`**, with
   `noiseInput_uniform : ∃ f, PolyTimeComputable f ∧ ∀ κ, f 1^κ = noiseInput κ`. It does not read the
   LWE parameter word.
   - **Justified.** `DrawSamplable` needs `U.Ω (y κ π) ≃ Coins`. The only registered
     `UniformSampler`, `bucketSampler`, reads its whole word as a numeral (`Ω y = Fin ⟦y⟧`), so no
     sampler reads `n`-bit seeds off `⟨1^n, ⟨1^m, ⦃q⦄⟩⟩`. A new sampler would be an unregistered host
     (COMMON §4.5).
   - **Rule 15 is kept.** The word is uniformly computable from `1^κ`: no advice and no κ-indexed
     program. `f` is polynomial-time, so the word has polynomial length. The core receives
     `⟨1^κ, ⟨noiseInput κ, seed⟩⟩` and must be one `PolyTimeComputable` map.
   - **`encodeSeed` cannot be chosen freely.** It is pinned by the sampler's encoding equation
     `U.enc (y κ π) w = encDraw κ π (e κ π w)`.
2. **`noiseWord e = [e < 0] :: bits |e|`**: sign-magnitude, modulus-free, with no width. This is the
   alternative the brief allowed, disclosed with its reason: the core does not see `q`. Honest
   algorithms reduce mod `q` after reading it through `Family.pairSndD_pairSndD_encode`.
   - The brief's `noiseWord (P) (w) e` signature lost both arguments as a consequence.
   - Question EF-D1-W3 is relayed below.
3. **Hypotheses `hs` and `CenteredSampleEq T`** on `noise_efficient_of_bitNoise`,
   `noise_efficient_centeredNoise` and `EfficientFamily.ofDyadic`. These come from EF-D1-SR1: see
   *Hypotheses* and question EF-D1-R1.
   - The `n : ℕ → ℕ` with `hn : n κ = t.eval κ` form, and `hgf` stated on `⟨1^κ, r⟩`, are refinements:
     they are no weaker, and `centeredNoise (T κ)` needs both.
4. **The LWE non-vacuity instance uses `centeredNoise 0`.** The brief used `centeredNoise 1`. See F01.
5. **`encode_injective` holds for `q ≤ 2^w`**, written at width `w + 1` (the `modulusWord`
   convention). The SIS form adds `β < 2^b`. Both match the families' own bounds, so this is a
   strengthening for the family use.
6. **Names.**
   - `SIS.dyadicScheduleParameters` and `dyadicScheduleFamily`, to avoid
     `Hashing.SIS.dyadic{Parameters,Family}`.
   - `params_uniform_of_schedule` takes `P` and field equations instead of a fixed constructor,
     which makes it more general.

**No silent weakening.** The structure fields are exactly the brief's, plus `noiseInput` and
`noiseInput_uniform` (change 1). No assumption is defined on `EfficientFamily`: consumers write
`DLWEAssumption F.toFamily`, which avoids a G45-01-style restatement. D1-P2 shows this, and I re-ran
it in phase 2.

## Rule 15 (uniform forms)

- **The noise sampler is in the contract form.** `EfficientFamily.noise_efficient` is
  `CoinSampling.SamplesEfficiently (P := fun _ => Unit) (fun κ _ => noiseInput κ)
  (fun κ _ => encodeSeed κ) (fun _ _ e => noiseWord e) (fun κ _ => (noise κ).sample)`.
  - The draw half is the `bucketSampler`, through `drawSamplable_residue` at `q = 2^{n(κ)}`.
  - The core half is a `PolyTimeComputable` map.
- **The parameter maps are uniform.**
  - LWE: `params_uniform` and `noiseInput_uniform`.
  - SIS: `params_uniform`.
  - Each is `∃ f, PolyTimeComputable f ∧ ∀ κ, f (1^κ) = …`.
- **No bare `∃ A : NUPPT, A.Computes`.** No `NUPPT` existential occurs in either file; the only
  `NUPPT` use is the reader `NUPPT.advInput_eq`. There is no `heff`/`ReductionEfficient`-style
  hypothesis, and no `Classical.choice`-defined machine.
- **The non-vacuity instances are real.**
  - `LWE.dyadicExample`: its `params_uniform`, `noiseInput_uniform` and `noise_efficient` are proof
    terms with axioms `[propext, Classical.choice, Quot.sound]` (D1-P3, re-checked in phase 2).
    Its noise is degenerate (F01).
  - `SIS.dyadicExample`: its `params_uniform` is likewise proved.
  - Neither instance claims hardness, and both docstrings say so.

## Duplication sweep (binding)

**Searches.**
- **TCSlib.** I searched the IO base and the records tip `64d51439` by name and by the shape of the
  conclusion:
  - `count_true_ofFn`, `natToList` lemmas, `bitsToNat`, `DrawSamplable`, `UniformSampler`
    instances;
  - `countTrue`/`onesCount`, signed differences, `natAbs`/`bits`, `true :: replicate _ false`;
  - polynomial-time numerals of `PolyExpr` values.
- **Remote heads.** I searched all 283 for the new names (above).
- **Mathlib** (`029db123dd`, `git grep`): `count_ofFn`, `count … = ∑`, `natAbs`/`bits` injectivity
  and `card_filter`. Its only relevant hit is `Finset.card_filter`, which the delivery uses.
- **Batteries and core:** no `count_ofFn`.

**Results.**
- **No undisclosed re-proof.** No public TCSlib or Mathlib lemma is restated.
- **Removed by the worker before delivery:**
  - a local `onesW`, now reusing `Randomized.onesW`;
  - a local `count true (ofFn g)` induction, now reusing `List.count_ofFn`.
- **The disclosed near-relatives are accurate:**
  - `signedDiff` vs `Hashing/SIS/CollisionOutput.lean`'s local `block`;
  - `noiseWord` vs `SIS.encodeSolution`;
  - `count_true_ofFn_eq_sum` vs `HardCoreGL.count_true_ofFn` and `List.count_ofFn`, from which it is
    derived;
  - `onesCount` vs ZK `countTrue`;
  - `natToList_two_pow` vs `CoinSampling.bitsVal_replicate_false_append_true` and Factoring's
    private `fac_natToList_one`/`_two`;
  - `drawSamplable_restrict`, a general contract lemma whose home is the frozen `Contract.lean`;
  - `Hashing.SIS.dyadic*`.
- **Two near-relatives are not disclosed** (**F03**). Neither is a re-proof.
- **No new sampler, loop or runner.** The bit-seed draw is `drawSamplable_residue` restricted and
  transported (`DrawSamplable.congr`). The arithmetic uses the registered `BinArith` hosts
  (`countLoop`, `le`, `sub`) and `Encoding.BinaryArith.fromLEPoly`.
- **Must-reuse items.** All are used or reasonably bypassed:
  - `polyTimeComputable_unaryPoly` stands in for `polyUnary`/`zerosPoly`;
  - `noiseSeeds`/`lweSeeds` are not needed, since no seed-level law is stated.

## Recount of the worker's evidence

I recounted from the raw files, binding each one to the reproduced sources by SHA-256. The tools are
in the evidence: `recount_seals.py` and `recount_controls.py`.

- **Build (C1).** For the 3 modules:
  - `summary.txt` gives rc 0, 0/0 errors and 0 `sorry`.
  - The three logs are empty (`e3b0c442…`), as `lean_check_tree.sh` leaves them on a clean compile.
  - The source hashes equal the head's.
- **Canonical seals (C6).**
  - **8 runs:** A and B, strict and coe, for the 2 owners.
  - Each sealed file, minus its one `attribute [local irreducible]` line, equals the head source
    byte for byte.
  - The seal line's names equal the delivered candidate list.
  - Each results line reads `PASS (rc=0, error lines=0)`.
  - Requests:

    | Owner | A-coe | A-strict | B-coe | B-strict |
    |---|---|---|---|---|
    | LWE | 1,269 | 1,270 | 1,271 | 1,272 |
    | SIS | 1,294 | 1,295 | 1,296 | 1,297 |

    These equal REPORT's table.
  - **What is sealed.** B differs from A by exactly `PolyExpr.eval` and its matcher. The coe-A
    requests include `LWE.bitNoise`, `centeredNoise`, `centeredValue`,
    `CoinSampling.DrawSamplable`, `SamplesEfficiently`, `modulusWord`, `residueEnc`,
    `Randomized.onesW` and `BinArith.countLoop`.
  - **Gap.** The delivered seal outputs keep the result lines but not the raw Lean logs. Phase 2
    re-ran coe-A with the recipe's own harness.
- **Paired controls.** Matched per example span:
  - **LWE:** 14 NEG and 14 POS. In the sealed run each NEG fails exactly once, no POS fails and there
    are 0 stray errors; the unsealed run has 0 errors.
  - **SIS:** 5 and 5, likewise.
  - **ALL_OK.**
  - The 15 new LWE definitions are all sealed. `ofBitSeeds` is covered only beneath `ofDyadic`'s NEG
    (I2).
- **Explicit-unfold scan:**
  - 170 + 44 tokens;
  - 0 foreign definitions passed;
  - 0 generated-equation references.
- **Axioms (C5).** 119 constants:
  - 92 `[propext, Classical.choice, Quot.sound]`;
  - 18 `[propext, Quot.sound]`;
  - 7 `[propext]`;
  - 2 `[]`;
  - no `sorryAx`.

  Phase 2 recomputed them independently.
- **Lint (C8).**
  - `style_lint`: 0 findings in 3 files.
  - `campaign_style_lint --check8b`: base 92 FAIL / 103 WARN over 542 files; head 93 / 103 over 544.
  - The only new line is the disclosed, brief-sanctioned
    `FAIL TCSlib/Cryptography/LWE.lean facade does not import child module …LWE.Efficient`.
  - Phase 2 reproduces this on the merged tree.
- **C2 downstream.** The worker could not reach the root (PFR/LeanAPAP oleans), which is F05.
  Phase 2 closes it.

## Hypotheses that weaken the result

- **`hs` on `noise_efficient_of_bitNoise`, and `CenteredSampleEq T` on
  `noise_efficient_centeredNoise` and `EfficientFamily.ofDyadic`.**
  - **What they are.** Each is the sample equation of `bitNoise`/`centeredNoise` at a seed of type
    `Coins`, read through the cast `bitNoise_Coins`/`centeredNoise_Coins`. It is true by `rfl` in the
    owner file.
  - **Why it is a hypothesis.** It cannot be derived through the published readers under the seal.
    `bitNoise_sample` and `centeredNoise_sample` are stated at `Fin _ → Bool` seeds, and relating
    them to `Coins`-typed seeds needs `bitNoise`'s definitional unfolding.
  - **Phase 2 confirms this with an extended demonstration.** With `bitNoise`/`centeredNoise`
    sealed, every attempt fails:
    - direct application;
    - `rw`;
    - `simp only`;
    - the cast round trip;
    - `rw` for `centeredNoise`.

    The two proposed readers pass by `rfl` unsealed (owner form).
  - **The E-SCOPE (EF-D1-SR1) is genuine.** It needs two one-line readers in the frozen
    `LWE/BitNoise.lean`.
  - **Consequence.** In the library, `CenteredSampleEq T` is provable only at `T = 0`
    (`centeredSampleEq_zero`, which goes through `centeredNoise_bounded`). So:
    - every `ofDyadic` family with non-zero noise must carry the hypothesis;
    - the generic theorems are fully proved but conditional;
    - EF-H4 and every later scheme instance on `ofDyadic` inherit the hypothesis until SR1 lands.
  - **Status.** It is not an axiom in disguise (it is true), and it is disclosed. The decision is
    Seyoon's: **EF-D1-R1**.
- **No other hypothesis weakens a target.**
  - `hW : 1 ≤ W.eval κ` gives `q ≥ 2`, which `Parameters` requires.
  - `hSB : S < 2^B` is the family's own `sqNormBound_lt_pow`.
  - `hc` (seed type) and `hgf` (the core's equation) are the content of the generic constructor.
  - `encode_injective`'s `q ≤ 2^w` and `β < 2^b` are the families' bounds.

## Findings

**Blockers: none. Majors: none.**

- **EFD1-F01 (minor; the subject of EF-D1-R1).** The LWE non-vacuity instance is
  `dyadicExample = ofDyadic … (.const 0) … centeredSampleEq_zero`, so `χ = centeredNoise 0`.
  - **What the instance exercises.** Its noise is the point law at 0, its seeds are 0 bits, and the
    bucket draw is over `Fin 1`. It shows that the structure is inhabited with every field proved,
    but it exercises the noise path only at seed length 0.
  - **What the brief asked.** The brief's instance was `centeredNoise 1`.
  - **Status.** The deviation is disclosed (statement change 4) and caused by SR1. The worker shows
    that with the readers, `ofDyadic … (.const 1)` compiles unchanged (`scope/SR1-probe.lean`,
    rc 0, axioms standard).
  - **Fix.** It is closed by EF-D1-R1 (A) or (B).
- **EFD1-F02 (minor, disclosed).** The size is 1,079 new lines against the brief's 350–650 ±40%
  (at most 910), so it is about 170 lines over.
  - The excess is the readers of the generic constructors, which repeat long hypotheses, and the
    generic bit-seed theorems.
  - No restatement is involved. No landing edit; noted for the size calibration of EF-H4.
- **EFD1-F03 (minor; disclosure).** Two near-relatives are missing from REPORT §7. Neither is a
  re-proof.
  - `LWE.natToList_bitsToNat`: `natToList (n+1) (bitsToNat r) = false :: ofFn r`. Compare
    `Candidates.natToBits_bitsToNat` (`Candidates/Arithmetic.lean:152`) with `natToList_eq` (`:104`),
    which give the width-`n` form `natToList n (bitsToNat r) = ofFn r`. The width-`n+1` form is new,
    and is derived from `natToList_length_listToNat`.
  - `LWE.seedModulusWord n = natToList (n+1) (2^n)`: a second spelling of
    `CoinSampling.modulusWord t κ (seedModulus t n hn κ)`. The bridge `modulusWord_seedModulus` is
    proved, but the relation is not listed as an overlap.
  - **Fix.** Disclosure only. Record both as a ledger note with W2.
- **EFD1-F04 (minor; attribution wording; optional landing edit).**
  - **The locator reads as Peikert's own.** `LWE.dyadicFamily` cites
    "[Pei16, Definition 4.2.3, power-of-two moduli]", and `SIS.dyadicScheduleFamily` cites
    "[Pei16, Definition 4.1.1, power-of-two moduli]". The ingested definitions are for general `q`;
    Peikert mentions power-of-two moduli only in §4.2's later discussion (ingested text, l. 167).
    The house form for a specialization is "…, explicit power-of-two specialization" (cf.
    `bitNoise`'s "[Pei16, Definition 4.2.1, explicit finite-bit specialization]").
  - **[Lem19] is outside the brief's list.** It is cited in `LWE/Efficient.lean`'s references and in
    `drawSamplable_bitSeeds`, but the brief's *Sources* do not list it and no reference file ingests
    it. It is the citation of the unmerged iO-base `CoinSampling/Buckets.lean` (#378), copied "as
    `CoinSampling/Contract.lean` cites it", not fabricated.
  - **The docstrings overstate what is proved.** The module docstring says "(exact draws: failure 0)",
    and `noise_efficient_of_bitNoise` says "seeds drawn from fair coins". The theorem proves the
    contract's failure bound of at most `2^{-κ}`; failure 0 is true, but no declaration states it.
  - **Fix.** A wording edit; no Lean change.
- **EFD1-F05 (minor; closed in phase 2).** The worker could not run C2: the root `TCSlib` needs
  PFR/LeanAPAP oleans that the Mathlib cache lacks.
  - Phase 2 rebuilt the root and both `audits/*/Checks` on the merged tree with snapshot #11's PFR
    oleans: rc 0, 0 errors.
- **EFD1-I1 (information; question EF-D1-W2).** `SIS/Efficient.lean` imports `LWE/Efficient.lean` for
  `natToList_two_pow` and `polyTimeComputable_twoPowWord`. This pulls `LWE/BitNoise` and the
  CoinSampling contract into the SIS facade's closure. It adds no hardness dependency.
- **EFD1-I2 (information).** `EfficientFamily.ofBitSeeds` has no isolated control pair. It is sealed,
  and its NEG is subsumed by `ofDyadic`'s (C14); its three readers are published.
- **EFD1-I3 (information).** Honest LWE algorithms now compose two uniform maps
  (`params_uniform`, `noiseInput_uniform`) and must reduce the sign-magnitude `noiseWord` mod `q`
  themselves. This is EF-H4's burden: state it in EF-H4's brief.
- **EFD1-I4 (information).** The worker's commits carry the worker's own `Claude-Session` trailer
  (`session_01PqpVTmDD9txtmcmydGy4q5`). As in earlier landings, the cherry-picks keep the messages
  verbatim.

## Landing

- **The branch.** `land/ef-d1-lattice-families` (`bd4c6f2d826b2fb91c02d720d8bd6b60c2a3795e`) is
  `iO/phase-a-base` plus maintainer-signed cherry-picks of the 4 commits. It is open as **draft PR
  #387**, with base `iO/phase-a-base` (see `phase2.md`).
- **LE-efd1-imp (the `LWE.lean` facade line).** `import TCSlib.Cryptography.LWE.Efficient` plus its
  `## Contents` entry.
  - #377 is now merged on the records branch (`bff0567b`), but the PR's base `iO/phase-a-base` is
    cut from REC and does not contain #377's `LWE.lean`.
  - So the line is added when this stack reaches the records branch, after #374, #378, #384 and
    #380: either on the merge, or as a one-line follow-up commit once `iO/phase-a-base` contains
    #377.
  - It removes the one new lint FAIL.
- **LE-efd1-cite (optional, F04).** The docstring wording.
- **If EF-D1-R1 is answered (A),** the SR1 landing edit is added before the PR leaves draft, and
  phase 2 is re-run on the changed files.
- **The gate.** A Codex gate reads the delivery before EF-H4 and the scheme instances build on it
  (brief, *Route*). It is to be staged.

## Questions for Seyoon

- **EF-D1-R1 (the `CenteredSampleEq` hypothesis; E-SCOPE EF-D1-SR1).** How should the sample
  equation of `bitNoise`/`centeredNoise` at `Coins`-typed seeds be supplied?
  - **(A, recommended)** Grant SR1 as a landing edit on this PR, before it leaves draft:
    1. Add the two `rfl` readers `bitNoise_sample_cast` and `centeredNoise_sample_cast` to
       `LWE/BitNoise.lean`. The text is the worker's `scope/EF-D1-SR1-BitNoise.patch.txt`.
    2. Drop `hs` from `noise_efficient_of_bitNoise`.
    3. Delete `CenteredSampleEq`, `centeredSampleEq_iff` and `centeredSampleEq_zero`, and the
       hypothesis on `noise_efficient_centeredNoise` and `ofDyadic`.
    4. Switch `dyadicExample` to the brief's `centeredNoise 1`.

    The maintainer drafts the diff, replays and re-seals. `BitNoise.lean` is in no open PR and not
    in S2-A's scope.
    - *Why:* the equation is true by definition in its owner. A hypothesis that every consumer
      carries, and that is provable only at zero noise, should not enter EF-H4.
  - (B) Land as delivered, and do SR1 as a separate small PR stacked on this one, before EF-H4
    lands.
  - (C) The worker's minimal form: add the readers and a theorem `centeredSampleEq T` (for every
    `T`), but keep the hypothesis-taking signatures.
  - (D) Keep the hypothesis form as delivered, permanently.
- **EF-D1-W2 (the shared helpers; the worker's question).**
  - **(A, recommended)** Accept as delivered now, and record a ledger follow-up. At the next
    shared-file window, promote `natToList_two_pow` and `polyTimeComputable_twoPowWord` (with
    `seedModulusWord`, F03) beside `CoinSampling.modulusWord`, and `drawSamplable_restrict` into
    `CoinSampling/Contract.lean`, then drop `SIS/Efficient`'s import of `LWE/Efficient`.
  - (B) Promote now, as a landing edit on #384's `Contract.lean`. This is a change to an open,
    gated PR.
  - (C) Leave them where they are, permanently.
- **EF-D1-W3 (the noise output form; the worker's question).**
  - **(A, recommended)** Accept the sign-magnitude `noiseWord`; honest algorithms reduce mod `q`
    (EF-H4's brief states it, I3).
  - (B) Require the residue form. This needs a new `UniformSampler` reading a pair component, or a
    core that recomputes `q` from `1^κ`.

**Not yet clear to merge — draft PR #387 stacked on `iO/phase-a-base` (#374, #378, #384, #380 unmerged);
EF-D1-R1 open; Codex gate to be staged; `LWE.lean` import is a landing edit.**
