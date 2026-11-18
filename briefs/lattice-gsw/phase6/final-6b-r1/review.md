# gsw-6b-statements · final r1 · phase-1 (static) maintainer review

**Interim verdict: ACCEPT WITH LANDING EDITS, pending phase 2 and the rulings below.** There is no blocker and no
major. There are three minors, all docstring-only and closed by the proposed landing edits LE-6b1 and LE-6b2, and seven
infos. Three questions come from the worker's own r3 deviations (G6B-W1–W3); I recommend accepting all three.

The delivery does what the brief and the checkpoint-1 feedback ask:
- **Checkpoint fixes.** All four are done. O2 now rewrites with Mathlib's `ZMod.valMinAbs_natAbs_eq_min` and has no
  `habs`. G15's sketch names `uprob_fst`. The census lists `decrypt_eq_decode_dotProduct` as MISSING beside
  `hybridPlant`. The admissions comparison now covers all 1,452 modules, including the new ones.
- **Reproduction and integrity.** Both series reproduce hash for hash on the issued base, and `src/` and `src-o2/` are
  byte-equal to the heads. Both manifests verify, with exact path sets.
- **Statements.** decls2 gives 136 ADDED / 0 / 0, five of them in `BitEncoding.lean` (O2).
  - There are exactly 24 admitted targets (23 r3 rows, with G17 split), each with a formula docstring, a source tag and
    a `**Proof sketch.**`.
  - G11 and L1 are proved citations. G14 and A2 are reader-only. G15 is stated over `fheView`'s projection.
- **Admissions.** 313 = 289 + 24 in 63 = 55 + 8 modules, name for name, recounted from the bound build logs.
- **Duplication.** No new declaration restates or re-derives a public lemma by name or by shape. I checked against
  `TCSlib/` at the base, the records tip, #366 and #368, and Mathlib. There are no private declarations at all.

I ran no Lean. Phase 2 replays the landing branches on the olean snapshot current at landing.

## What was reviewed

- **Delivery.** `inbox/fills/gsw-6b-statements/` on `exchange/pass-shelat-ch5-8`.
  - Final: `3b340824dde77433b2135a3c8d20c7ed194cf18c` ("stmt gsw-6b: final", 2026-11-17 23:48 UTC). Its parent is
    `f01fae49fe6c987696b310395052e2f7a637302d` (another job's commit).
  - Checkpoint 1 was `1e0647b99de8ee4d11722b5bad862fe40837a2ce`.
  - The final commit is unsigned (`gpgsig` 0) and touches only that path. No later exchange commit touches it (the
    exchange tip at review is `c05e1cb9fdb85f4e9d9b90339d00eeb562639a0c`).
  - I extracted the folder with `git archive` into an empty scratch directory. It holds 2,688 files: `REPORT.md`
    (462 lines), `patches/o2/` (1 patch), `patches/stmt/` (5 patches), each with `COMMITS.tsv`, `src/` (12 files),
    `src-o2/` (1 file), and `evidence/` (2,664 files plus its manifest).
- **Heads (REPORT §0).**
  - O2 `owner/o2-decode`: `5bd5ada5f42c5e1228ea84ad70f4d8c52a3644fd`.
  - Statements `stmt/gsw-6b`: `7a8145468202f908f6a1e41638fc793c2313b850` (Branching, DecryptFormula),
    `dd9f00f484a7e89390ce8a68b19cac773fb6f9b1` (Bootstrap, Circular), `1378740f5f516f8047fd9cf83e56414091dde8af`
    (Leveled, LeveledSecurity), `5c8f81cdd83aca13d737cea3fd0d03fb37d9f9b8` (Ratio, PolyRatio, Asymptotic) and
    **`8f92fe7d53967bc488a4075fb38210e7d40b9031`** (facades).
  - Base `3e51b5f28900db6190f1eb2e6d207d27ee15d541`, unchanged.
- **Contract.** `issued-6b-r1/` (brief, addendum, `targets.txt`, `census.txt`, `pins.txt`, `base-sorries.txt`,
  `closures.txt`, `order.txt`, `tools/`), plan section r3, `rulings.md` (P6-Q1..Q19 and the Q19 refinement), Q-6B-1 A,
  `checkpoint1-6b-review.md` and the feedback relayed on 2026-11-17 (decision log).
- **Moved since the base.**
  - The records tip is `5ed4ca865597d56e59e079eb7ae90c21b9b0617b`; #347 and #355 have merged into it.
  - #366 (`land/gsw-6a-fills` `597fb736e545706a058cc212243a13f6dadfeceb`) and #368 (`land/gsw-6b-owner-prereqs`
    `1953898b18a33ab2cd533820c5754a1aacffeb44`) are open drafts. Gate 50 closed CLEAR on both.

## Checks

| Check | Result |
|---|---|
| **Integrity** | Top `SHA256SUMS`: 2,687/2,687 OK. `evidence/SHA256SUMS`: 2,664/2,664 OK. Both path sets equal their manifests exactly: no missing or extra file, and no `./`. The diff of the final commit touches only `inbox/fills/gsw-6b-statements/`. |
| **Base** | `issued-6b-r1/tools/mkbase.sh`, run in a scratch repository whose object store points at the records clone, prints `STEP1 04947bcf… tree 8eca9617…` and `BASE 3e51b5f28900db6190f1eb2e6d207d27ee15d541 tree b69a66a385ca3439d56af1d6b9791b5847984fde`. |
| **Reproduction** | Sparse worktree, detached at the base. `git am` per patch, with each row's committer name, email and date from `COMMITS.tsv` and `commit.gpgsign=false`. All six hashes reproduce in order (`5bd5ada5…`, `7a814546…`, `dd9f00f4…`, `1378740f…`, `5c8f81cd…`, `8f92fe7d…`), none signed. `src/` is 12/12 byte-equal to `8f92fe7d`, and `src-o2/` is byte-equal to `5bd5ada5`. `git diff --stat` base..head lists exactly the 9 new files and the 3 changed ones (+2,170/−1; the −1 is the GSW facade's title line). |
| **Checkpoint fixes** | **F01:** `decode_iff_mem_Ico` rewrites both distances with `ZMod.valMinAbs_natAbs_eq_min`, and `habs` is gone. The sketch names the lemma. **F02:** G15's sketch (`Circular.lean:131–136`) names `acceptProb_def`, `acceptProb_comp_equiv` and `uprob_fst`. **F03:** G6's sketch (`DecryptFormula.lean:158–162`) points at the owner-side `decrypt_eq_decode_dotProduct`, and the census lists it as MISSING beside `hybridPlant` (`census/reader-census.md:121–160`). `Scheme.lean` is untouched. **F04:** the admissions comparison covers all 1,452 modules (see *Admissions*). Against checkpoint 1's `src/`, the four checkpoint files differ only in the two sketch paragraphs. |
| **O2** | The diff base → `5bd5ada5` is insertions only: two docstring entries, plus `decodeLo`, `decodeHi`, `decodeLo_eq`, `decodeHi_eq` (`rfl`) and `decode_iff_mem_Ico` (`BitEncoding.lean:118–172`), proved, with no `sorry`. decls2 at the O2 head: exactly 5 ADDED. The headers match r3 §H5.8 and the brief, every declaration says "Glue", and the theorem has a sketch. The issued `o2check.py` (re-run): moduli 2..2000, 0 mismatches. The remaining inline step `hsub` (the two-case value of `v − ⌊q/2⌋`) has no `ZMod` lemma in Mathlib. My grep of `Mathlib/Data/ZMod/` finds only `ZMod.val_sub` for the first case; the two-case facts exist only for `Fin` (`Fin.coe_sub_iff_lt`, `Mathlib/Data/Fin/Basic.lean:306`). Nothing else in the file changes. |
| **decls2** (pinned `fa81981a…`) | Base → `8f92fe7d` over the 12 files: **136 ADDED, 0 CHANGED, 0 REMOVED**. This is line-identical to the delivered `decls2-final-r2.txt`. The `simps` projections `fheView_fst`/`_snd` and `Parameters.ofFamily_lwe`/`_width` bring the new names to 140. |
| **Targets** | My comment-stripped scan finds 24 `sorry`, exactly one in each target: Branching 3, DecryptFormula 6, Bootstrap 5, Circular 1, Leveled 2, LeveledSecurity 2, PolyRatio 3, Asymptotic 2. There are none in `Ratio.lean`, `BitEncoding.lean` or the facades. Each of the 24 has a docstring with the formula, a `[TAG, loc, anchor]` tag and a `**Proof sketch.**`, checked by script. The row map (REPORT §4) is complete: **G11** `encrypts_evalKey` and **L1** `encrypts_levelKey` are proved citations (`rw [evalKey_eq]`/`rw [levelKey_eq, evalKey_eq]`, then `encrypts_encrypt`/`encrypts_keygen_encrypt`). **G14** and **A2** are reader-only (`weakCircularSecure_iff`, `weakCircularSecureFamily_iff`, `Iff.rfl`), and no `distAdv_fheView_le` or `fheView_negligible` exists. **G15** is stated over `fun r => ((fheView P χ μ r).1, (fheView P χ μ r).2.2)`. |
| **Definitions and readers** | Every `def`/`abbrev` has its reader, by script: `_eq` (rfl), `_iff` (Iff.rfl), the case readers of `bootGate` (3) and `levelGate` (2), `literalCts_castAdd`/`_natAdd`, `_length` for the four encodings, and non-simp `simps` for `fheView` and `Parameters.ofFamily`. The computable definitions are not `noncomputable`. Only `levelTerm` and `challengeTerm` (real-valued) are. |
| **Statement fidelity** | I read all nine files against r3 §H5.9–§H5.16 and the brief. REPORT §5 lists 22 deviations, all of them disclosed. Beyond checkpoint 1 (which covered G1–G15, G18): **L1–L3** match r3 §H5.13. `levelKey` encrypts `keyBits (ss d.castSucc)` under `pks d.succ`, and L3's output level `(Cc.toNANDForm hC).depth` is right because `layerNAND_depth` (N10) preserves depth exactly. **L4** is true as stated. With `hybridPlant`'s order (positions `< j` encrypt `0`, `j` planted, `> j` key bits), the gap at `j` is `adv(b = true) + adv(b = false) + 2·N·ε_LHL`. The reduction may plant `pk_{e+1}` because `s_{e+1}` occurs only in the level key `e + 1`, which `H_{e+1}` has already replaced; level keys below `e` use `pk_{e'+1}` with `e' + 1 ≤ e`. **L5:** the two-chain bound is right. `H_0(μ)` is `challengeDist` on phase 5's `realView`, so `challengeTerm` is exactly `distAdv_encrypt_le`'s right-hand side. **G16/G17:** `8·4^33·2 = 2^70` checks. With `8y ≤ pBoot·B < q`, `q ≥ 8y + 1 ≥ 4y + 2` for `y ≥ 1`, which gives `2y < ⌊q/2⌋`. With r3's `4` it fails at `q = 4y + 1` (G6B-W1). **A1/A3** match r3 §H5.16, with the challenge reductions added to (A4) (G6B-W2). |
| **Sources** | No `[Gen09]`. The P6-Q19 B disclosure is in the module docstrings of Leveled, LeveledSecurity, PolyRatio and Asymptotic, and each leveled declaration refers to it. Every `pNNN-bNNN` anchor in the 9 new files exists in its tag's ingest at the base: 123 checked, 0 missing (script `anchors.py`). But see G6B-F03. |
| **Hygiene** | No `native_decide`, `admit`, `axiom`, `@[simp]`, `attribute`, `show`, `change` or `delta`. The only `@[simps …]` carry `isSimp := false`. There is no `private` declaration. The only `unfold`s are of the file's own `bootGate` (×3) and `levelGate` (×2), in their case readers. Every name passed to `rw`/`simp only` is a lemma or the file's own reader. No micro sign, tab or trailing space. |
| **Widths and sizes** | Maximum width 99. Lines: Branching 179, DecryptFormula 220, Bootstrap 351, Circular 146, Leveled 283, LeveledSecurity 351, PolyRatio 174, Asymptotic 324, Ratio 59, BitEncoding 200, facades 57 and 40. With r3 §H7's upper fill estimates the largest files reach Bootstrap 791, LeveledSecurity 721 and Asymptotic 604. All stay under 1,000; these three are over the 600 target (G6B-F07). |
| **Lint** | `style_lint` (base blob) on the 12 files: 0 findings. `campaign_style_lint TCSlib/Cryptography --check8b` on sparse base and head checkouts: **92 FAIL / 104 WARN** over 529 and 538 files, with identical FAIL/WARN line sets. |
| **Clash** | The 135 new short names, grepped as declarations in `TCSlib/` and `audits/` at the base, the tip, #366 and #368, hit only unrelated namespaces: `Coins` (`PPT`, `SecureComputation.Hybrid`, `ZeroKnowledge.Interaction`), `PublicKey` (`RSA`) and `select` (`Turing.Cfg.select`, `Randomness.Rejection.select`). Since the base, the tip and #366/#368 add 87 declarations and change or remove none (decls2 base → tip×#366×#368). Their short names meet a 6b token only once, the intended `decrypt_eq_decode_dotProduct` in G6's docstring. All 129 backticked TCSlib names of the 6b docstrings that are declared at the base are still declared at that merge. |

## Evidence recount (from the raw logs)

- **Build binding.** Every module of `root-final/summary.txt` has its log at the stated run, with rc 0 and 0 errors in
  both forms, and its recorded source SHA-256 equals the blob at `8f92fe7d`: 1,452/1,452. The runs are the bootstrap at
  the base (270 modules), the root at the pre-review head `a855e111` (1,154) and `sweep-final-r2` at `8f92fe7d` (28).
  - **Staleness check** (`stale.py`). 12 modules have a source that differs between their earlier build and the
    final head: the 9 new modules, `BitEncoding` and the two facades.
  - No module bound to an earlier run has any of them in its import closure at the final head.
  - The rebuild set that requires is exactly the 28 of `sweep-final-r2`.
  - `a855e111` itself is not delivered. The check therefore uses the root run's recorded source hashes, and the base
    blobs for prefix modules.
- **Admissions** (`admit.py`). I took the `sorry` warnings of the 1,452 bound logs, mapped each to the declaration name
  at its position in the final source, and compared against `base-sorries.txt` plus the 24 targets: **313 in 63, 0
  differing modules.** At the O2 head: 289 in 55 (worker's graph scan; O2 adds no `sorry`).
- **Axioms** (`AxiomProbe-r2.log`). 176 constants (153 declarations and 23 auxiliaries). `sorryAx` reaches exactly
  28 of them:
  - the 24 targets;
  - `fheEvalCircuit` and `fheEvalCircuit_eq`, through N2 `nandGadget_correct` only;
  - `leveledEvalCircuit` and `leveledEvalCircuit_eq`, through N2, N12 `layerGates_acyclic` and N13 `layerOutput_lt`
    only.

  This is exactly the brief's prediction. There are no other axioms, and O2's constants are standard. At a landing
  that contains #366 all 6a targets are proved, so phase 2 expects `sorryAx` in the 24 targets only.
- **Seals** (`seals.py` over `rule10/r2/*/seal/run-*/mods/*.log`). At the final head, over 11 owners (the 9 new
  modules and the 2 facades), every variant has 0 errors in both forms, one `SEAL-END` per log and
  `requested = verified` at install and EOF:
  - A: 10,069 requests;
  - B: 10,075;
  - coe-A: 10,059;
  - coe-B: 10,065.

  `BitEncoding` has 9/9/9/9 requests at both the O2 head and the final head, also with 0 errors. The seal source hashes
  equal the heads' blobs, and the per-owner counts equal REPORT §9.
- **Controls.** Final: 45 rows, 9 owners × (unsealed negative + strict and coe negative and positive). `BitEncoding`:
  5 rows at each head. `ALL_OK` holds. In the raw logs every sealed negative control has exactly 1 error and every
  other control has 0.
- **Probes** (P1–P8). No `native_decide`.
  - P3 (O2): 62 kernel `decide` theorems for `2 ≤ q ≤ 63` with standard axioms, plus `#eval` to 2,000. The negative
    control is refuted.
  - P7: the constants hold (1,746 and 6,984 grid checks, 0 violations; `decDepth` grows by about 7–11 per doubling
    of `ℓ`).
  - P8: elaborates.
  - Partial runs are disclosed (G6B-F06).

## Duplication (policy §1; G44-01, G45-01, G48-01, GF-F01–F03, BS-F02, Gate 50 U1–U3)

I searched by name (all 135 short names, see *Clash*) and by shape, at four revisions: the base, the records tip,
#366 and #368, and in Mathlib `029db123` and core.

**Definitions.**
- **Type abbreviations** (`PublicKey`, `Secret`, `Coins`, `KeySeed`, `FheView`, `Seeds`, `LevelCoins`, `LeveledSeeds`,
  `LeveledView`). Phase 5 and Regev name none of these types: Regev's `keygen` spells its seed type inline, and
  `Regev/Experiments.lean:136` has only a local `let`. LWE has no challenge-type abbreviation.
- **`Family.RatioBounded`.** No ratio predicate exists. The only `modulus ≤ …eval…` is the `Family` field
  `modulus_le_pow`.
- **`Parameters.ofFamily`.** Nothing maps a family to GSW parameters.
- **Encodings.** They are thin wrappers over `Encoding.Modular.encodeMatrix` and `LWE.encodeChallenge`, and there is
  no GSW encoding.
- **`WeakCircularSecure`/`Family`.** There is no circular-security predicate anywhere.
- **`ReductionEfficient`/`Leveled…`.** No GSW asymptotic statement exists. `DLWEAssumption` is used only in
  `LWE/Assumption`, `SampleSchedules`, `Pseudorandom/Generators/LWE/Basic` and `Lossy/Experiments`.
- **The hybrid layer** (`levelHybrid`, `levelMsgs`, `levelAssemble`, `levelReduction`, `levelTerm`, `challengeDist`,
  `challengeTerm`). It is built from the public `hybridPlant`, phase-5 `reduction` and `encrypt` as terms, with no
  local hybrid lemma.
- **`levelGate`** is a `dite` over `bootGate`, and **`literalCts`** is `Fin.append` with phase-5 `homNot`, which is
  reused, not copied.

**Targets.** None is an exact restatement.
- **A1** has no phase-5 counterpart: phase 5 is concrete only (`distAdv_encrypt_le_of_width`).
- **G17** composes G12/L3 with G16 under different hypotheses.
- **G18** is G10 composed with N3–N4.
- **`decDepth_le`** is a *weakening* of F10's `modSumDepth_le`: `ℓ` replaces `⌈log₂ q⌉` behind `decDepth`.
  `targets.txt` makes it a target, and the worker discloses it (G6B-F05, info).
- The near-relatives in the brief's list are confirmed different: `eval_encrypts`/`decrypt_keygen_eval`, `homGate`,
  `Encrypts.nand`, `vecMul_secretVector_augmented`, `gadget_mulVec_decomposeVec`, `decode_codepoint_add`. The three
  `polyExpr_mul` copies are cited, not a fourth added.

**Inline proofs.**
- **O2.** `hsub` has no `ZMod` lemma (see *O2*); `hcast` is a cast identity; `hh : q/2 < q` is one `omega`.
- **`Parameters.neZero_columns`** derives `P.width ≠ 0` from `2 ≤ q ≤ 2^ℓ` by `rw [h, pow_zero] at hle; omega`. This
  is core's `Nat.one_lt_two_pow_iff` (`1 < 2 ^ n ↔ n ≠ 0`, `Init/Data/Nat/Lemmas.lean:1123`), used backwards. It is a
  two-line case contradiction and was present at checkpoint 1. I grade it info, borderline like Gate 50's U3, with an
  optional proof-only LE-6b3 (G6B-F04).
- The `_length` proofs use only library lemmas (`encodeMatrix_length`, `encodeChallenge_length`,
  `List.length_flatten`, `List.ofFn_const`, `List.sum_replicate_nat`).

**Cross-file copies.** There are none: no `private` declaration exists in any of the 12 files.

## Merge interaction and landing shape

- **`git merge-tree --write-tree`** is clean (rc 0) for each pair:

  | With | O2 head | stmt head |
  |---|---|---|
  | tip `5ed4ca86` | tree `293fd00a` | tree `1d9fd4d5` |
  | #366 `597fb736` | tree `ceca9f2e` | tree `7c66ca47` |
  | #368 `1953898b` | tree `97c0f35b` | tree `40aa06d2` |

  The chain tip × #366 × #368 × O2 × stmt is also clean (scratch commits; final tree `35574eb6`).
- **Shared paths.** None. Against their merge base `036d8239`, #366, #368 and the tip touch none of the 12 delivery
  paths.
- **Semantic interaction.**
  - #368 adds `decrypt_eq_decode_dotProduct`, character-equal to the census proposal, and the `hybridPlant` reader,
    named `hybridPlant_eq` where the census proposed `hybridPlant_apply`. Both fill prerequisites are therefore met
    once #368 merges.
  - #366 proves N2, N12 and N13, so `fheEvalCircuit` and `leveledEvalCircuit` lose `sorryAx`. Three 6b docstrings
    then become stale (G6B-F01; LE-6b1).
  - Admissions expected at landing: 192 (tip × #366 × #368) + 24 = **216**.
- **Proposed landing.** It waits for #366 and #368 to merge (base on that tip).
  1. **PR O2** `land/gsw-6b-o2`: the O2 commit replayed on the tip. It touches `BitEncoding.lean` only (+58/−0).
  2. **Statement PR** `land/gsw-6b-statements`, stacked on PR O2: the five statement commits, then one landing-edit
     commit with LE-6b1 and LE-6b2 (and LE-6b3 if ruled and if it compiles).
  - Phase 2 then replays both on the snapshot current at landing:
    - the 18 `DOWN` modules, the 9 new modules, the facades and the root, all rc 0;
    - admissions +0 at O2 and +24 at the statements;
    - axioms: `sorryAx` only in the 24 targets;
    - seals and controls with no new failures;
    - decls2 136/0/0 plus LE-6b3's no-op on headers;
    - lint unchanged.
  - Gate 46 then audits both PRs.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| G6B-F01 | minor (stale prose at landing; the G50-01/G50-02 pattern) | Once #366 and #368 merge, which the landing requires, three docstring passages become stale. (a) G6's sketch (`DecryptFormula.lean:158–162`) calls `decrypt_eq_decode_dotProduct` "**MISSING** at the base", but #368 adds it with the identical statement. (b) The `fheEvalCircuit` and `leveledEvalCircuit` docstrings (`Bootstrap.lean:193–194`, `Leveled.lean:174–175`) say "While 6a's N2 (N12, N13) is admitted, `sorryAx` reaches this definition…", but #366 proves them. (c) L4's sketch (`LeveledSecurity.lean:311`) says "`hybridPlant`'s planted position", where #368 now provides the reader `hybridPlant_eq`. | **LE-6b1** (docstrings, −10/+6; landing after #366/#368). |
| G6B-F02 | minor (docstring accuracy) | `PolyRatio.lean:48` and REPORT §6 describe the settled constant as "(r3 §H6: `c < 2^70`)". The constant is exactly `2^70` (`8·4^33·2`). r3's draft bound `c < 2^70` held only with r3's factor `4` (`2^69`), which the worker replaced by `8` (G6B-W1). | **LE-6b2** (the sentence says "constant `2^70`; r3 §H6 drafted `c < 2^70` with the factor `4`"). |
| G6B-F03 | minor (brief deviation, partly disclosed) | The brief (from the P6-Q19 refinement) says the leveled docstrings cite only [BV11, Thm 3.1, Def 3.6], [BV14, Thm 2.14 first part, Thm 3.7] and [AP14, §5.3]. `Leveled.lean` also cites [BV14, Def 2.12] (compactness), [BV14, §3.3] and [Bar89, Thm 1] (literal inputs), yet its module docstring says the statements cite the three sources "only". `LeveledSecurity.lean` also cites [GSW13, §3.2, Lemma 1] and [BV11, Def 3.1], which it discloses, and [BV14, §2.5], which it does not. All of these are ingested, their anchors exist, and they attach to sub-facts (one-key steps, the view, literals, compactness), never to the key chain or the hybrid order. That is within the ruling's text ("citing only ingested sources"). | **Q-6B-F1**. Recommended: accept the citations and make the two sentences accurate (**LE-6b2**). |
| G6B-F04 | info (borderline re-derivation) | `Parameters.neZero_columns` (`DecryptFormula.lean:65–70`) proves `P.width ≠ 0` by the case contradiction `rw [h, pow_zero] at hle; omega` instead of core `Nat.one_lt_two_pow_iff`. It was present at checkpoint 1, which I did not flag. | Optional **LE-6b3** (proof only; dropped if it fails to compile, as LE-gf4). Seyoon's call in Q-6B-F1. |
| G6B-F05 | info (specialization, disclosed) | `decDepth_le` (G8) is F10's `modSumDepth_le` at `M = N` behind `decDepth`, weakened by `⌈log₂ q⌉ ≤ ℓ`. It is an admitted target by `targets.txt`, and the worker discloses it in *Overlap and reuse*. Once #366 lands, F10 is proved and the U13 fill is about 3 lines (its sketch names `modSumDepth_le`, `Nat.clog_le_iff_le_pow` and `Nat.clog_mono_right`). Not a restatement: the right-hand side differs. | Keep as delivered (**Q-6B-F2** A). Gate 46 may ask; the disclosure answers it. |
| G6B-F06 | info (probe coverage, disclosed) | **P2c** (G3 numeric noise) was stopped for time; only the noise-free part ran (7 formulas × 4 inputs). **P5b** (`fheEval` on the padded XOR circuit) completed 1 of 4 inputs before a container restart. One input takes over an hour; P5a covers `bootNAND` on all 4 pairs. **P6** ran the depth-2 parity twin `NAND(x₀, NAND(x₁))`, which has a level gap, on 4/4 inputs, instead of 6a's P9 XOR and odd-gap circuits (cost). **P4**'s kernel attempt on G6/G7 got stuck; `#eval` covers them. No statement was found false. | Record. The fills prove these statements; probes are evidence only. |
| G6B-F07 | info (size) | The surface is about 2,090 lines in the 9 new files, above the brief's 1,300–1,800 estimate (mostly docstrings and the reader layer). Fill projections: Bootstrap ≤ 791, LeveledSecurity ≤ 721, Asymptotic ≤ 604, all under 1,000 and over the 600 target. | Watch at the U14/U17/U19 fills. |
| G6B-F08 | info (process) | (a) The lead again stopped a stray `git clone` with `pkill -f` instead of by PID (handoff rule 4), and disclosed it. (b) A probe was OOM-killed at 13.2 GB, and the pool shrank from 3 to 2 slots. (c) The root build was resumed after the 2-hour tool limit. (d) The probe sub-agent stopped on a usage limit, and the lead re-ran its last runs. (e) The split differs from the suggested one: the lead wrote every statement, and the sub-agents `seal` and `probe` only verified. Every item is recorded in REPORT §3 and §14. | Record. |
| G6B-F09 | info (census naming) | The census proposes `hybridPlant_apply`; #368 landed the reader as `hybridPlant_eq` (Gate 50 CLEAR). | LE-6b1 names `hybridPlant_eq`; no census edit (it is evidence). |

## Questions for Seyoon (recommended option first)

- **Q-6B-W1 (G16's factor; worker's question).**
  - **A (rec.)** Accept G16 as `8·(ℓ·bootNoise) ≤ pBoot·B` with `pBoot`'s constant `2^70`, and keep G17's r3 hypothesis
    `pBoot·B < q`. With r3's `4`, G17 would need `4y + 2 ≤ q` but get only `4y + 1 ≤ q` (counterexample `q = 4y + 1`);
    I checked this.
  - **B** Keep `4` in G16, and state G17's hypothesis as `pBoot·B + 2 ≤ q`.
- **Q-6B-W2 (`LeveledReductionEfficient`; worker's question).**
  - **A (rec.)** Accept the delivered form: one `D'` also dominates the two challenge reductions
    `reduction P_κ μ' (challengeDist …)` that L5's last step needs. Without them A3 would not follow, and building an
    NUPPT for `challengeDist ∘ D` is the out-of-scope machine construction.
  - **B** A separate hypothesis for the challenge step.
- **Q-6B-W3 (L4/L5 shape; worker's question).**
  - **A (rec.)** Accept `levelTerm … μ e j D` and L5's bound `∑ₑ ∑ⱼ (levelTerm μ₀ + levelTerm μ₁) + challengeTerm μ₀
    μ₁`. The level reduction must simulate `Enc_{pk₀}(μ)`, so r3's μ-free `levelTerm` with `2·∑` was inconsistent with
    r3's own `levelReduction (… μ …)`.
  - **B** `2·∑ max_μ levelTerm`.
- **Q-6B-F1 (landing edits).**
  - **A (rec.)** Apply LE-6b1 and LE-6b2 (docstrings only) in one landing-edit commit on the statement PR, with the
    landing on the tip after #366 and #368. Also apply LE-6b3 (proof only), dropped if it fails to compile.
  - **B** LE-6b1 and LE-6b2 only.
  - **C** LE-6b2 only, leaving G6's and L4's sketches to the U13/U17 fills. Not recommended: Gate 50 graded the same
    staleness minor.
- **Q-6B-F2 (`decDepth_le`).**
  - **A (rec.)** Keep it an admitted target, as `targets.txt` makes it. The U13 fill proves it from F10.
  - **B** Prove it at landing as a citation (admissions 24 → 23; a new proof in a statement PR).

## Proposed landing edits

`landing-edits-proposed.diff` (141 lines; uncompiled; it applies in order to `8f92fe7d`, which I checked with
`git apply`, and to the landing merge, since no path is shared). Widths stay ≤ 100.
- **LE-6b1** (G6B-F01, F09; only for a landing on a tip that contains #366 and #368), 4 files, docstrings:
  - G6's sketch says `decrypt_eq_decode_dotProduct` is in `GSW/Scheme.lean` (owner-side, ruling Q-C1).
  - `fheEvalCircuit` and `leveledEvalCircuit` drop the "while … is admitted" sentence.
  - L4's sketch names `hybridPlant_eq`.
- **LE-6b2** (G6B-F02, F03), 3 files, docstrings:
  - PolyRatio's deviation sentence gives the constant `2^70`.
  - `Leveled` says its extra citations are for compactness and the literal inputs.
  - `LeveledSecurity` adds [BV14, §2.5] to its disclosed list.
- **LE-6b3** (G6B-F04, optional), `DecryptFormula.lean` proof only:
  `⟨Nat.mul_ne_zero (Nat.succ_ne_zero _) (Nat.one_lt_two_pow_iff.mp (Nat.lt_of_lt_of_le P.lwe.modulus_ge_two
  P.modulus_le))⟩`.

No edit changes a declaration header; decls2 stays 136/0/0.

## For the worker

No action is needed: the delivery is complete. If Seyoon rules otherwise on Q-6B-W1–W3, the maintainer re-issues with
the change.

## Evidence

`gsw-6b-final-r1-phase1-evidence.zip` (SHA-256 in `evidence-SHA256SUMS`). It contains `PROVENANCE.txt`, an internal
`SHA256SUMS`, `scripts/` (`repro.sh`, `decls.py`, `sorries.py`, `bind.py`, `stale.py`, `admit.py`, `seals.py`,
`anchors.py`) and `out/`:
- integrity and `mkbase.sh` output;
- reproduction;
- decls2 (final, and base → tip × #366 × #368);
- the new-declaration and sorry scans;
- binding staleness and admissions;
- the seal recount;
- anchors;
- campaign-lint line sets;
- merge-tree.
