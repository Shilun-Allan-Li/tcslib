# GSW 6b U18+U19 `gsw-6b-u18-u19` · final r1 · maintainer review (phase 1 static, phase 2 Lean replay)

**Verdict after phase 2: ACCEPT. No landing edit.** The five targets G16, G17 (pure and leveled) in
`GSW/PolyRatio.lean` and A1, A3 in `GSW/Asymptotic.lean` are proved as stated. **A1 and A3 are proved from their frozen
`heff` hypotheses, which stay** (each still takes `hF`, `heff`, `hm`). The one allowed public helper
`Parameters.ofFamily_columns_le` is added with the brief's statement byte for byte, and nothing else public. A1 and the
helper are standard-only; the other four reach `sorryAx` only through the allowed frozen targets of U14-U16 and U15-U17.
Phase 2 passed with no new finding. The details are in [`phase2.md`](phase2.md).

- **Findings:** 0 blockers, 0 majors, 0 minors, 3 info.
  - U1819-F01: `m·B ≤ bootNoise P (m·B)` is derived inline here and in U14+U16's G12 (U1416-F01; a cleanup item).
  - U1819-F02: A1's and A3's frozen sketches were left unrefreshed; they still name `ofFamily_width` and
    `dimension_le` where the proofs cite the helper.
  - U1819-F03: small inline repetitions (the `hq`/`hmκ` blocks twice; phase 5's `2·(N·ε) ≤ N·2^{−κ}` step;
    nonnegativity of `distAdv`), none a published lemma.
- **Phase 2 (2026-11-19, 01:36–02:21 UTC, both units of this review in sequence).**
  - **Build:** B6 + U18+U19: 6/6 rc 0, including the root `TCSlib`, 0 `sorry` warnings, admissions **37 in 14**.
    Stacked on the records tip (with U12/U13): 12/12 rc 0, admissions 28 in 12. The two owned oleans are byte-identical
    in both trees.
  - **Axioms:** the census covers all 37 stored constants; 32 standard, 5 reaching `sorryAx` only through allowed
    names; the same names and sets as the worker's. In the full 6b stack (with U14+U16 and U15+U17) all five targets
    are standard-only.
  - **Seals:** canonical coe-A and seal B, 0 errors: PolyRatio 1,394/1,395, Asymptotic 1,653/1,654 requests verified.
    An extra own-definition seal shows that no proof in `PolyRatio.lean` reads `ofFamily`'s or `pBoot`'s body.
  - **Controls:** 4 liveness pairs, the helper's own included, ALL_OK. **Unfold scan:** 0 definitions.
  - **Lint:** unchanged. **Snapshot #11:** 0/0/0 before, mid-run and at the end.

## What was reviewed

- **Delivery.** `inbox/fills/gsw-6b-u18-u19/` on `exchange/pass-shelat-ch5-8` at
  `4da71016e503c4f64ea2cee0ed2f6b748b1a32ec` (the origin tip when read). The final commit is `c414248e3` ("fill
  gsw-6b-u18-u19: final"); the folder is unchanged after it.
  - The checkpoint `5fb0d4b83` and the final are unsigned and touch only `inbox/fills/gsw-6b-u18-u19/`. The checkpoint
    delivered the same head: `src/` and `patches/` are unchanged between them.
  - Extracted with `git archive`: 485 files, namely `REPORT.md`, `SHA256SUMS`, 2 patches with `COMMITS.tsv`, `src/`
    (2 files) and `evidence/` (478 files).
- **Contract.** The issued pack at the records pin `27e53754`: `rulings.md`, `COMMON.md`, `U18-U19/brief.md`,
  `dup-sweep.md` (§0, §U18-U19), `targets.txt`, `base-sorries.txt`. Handoff §2 rules 10 and 15; `policy.md` §1–§3.
- **Rulings in force.** Q-6BF-1 A (EF-R1 is separate; A1/A3 are filled **from `heff`**, `Asymptotic.lean` keeps its
  statements), Q-6BF-3 A (exactly one public helper here, `Parameters.ofFamily_columns_le`), Q-6B-W1 A (factor `8`,
  constant exactly `2^70`), efficiency ruling Q2 A (A1/A3 statements kept), Gate 46's type-level Rule 10 on `ofFamily`.
- **Base and records tip** as in the U15+U17 review: B6 = `bff0567b…`; records tip `c87eb403` (later `a25338e0`),
  `TCSlib` tree `745bf4b4` = B6 + U12/U13.
- **Tools.** Phase 1 used `git` and `python3 -I` only; scratch under
  `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g6b-u1517-1819/`. Nothing was
  committed on any ref or pushed.

## Checks

| Check | Result |
|---|---|
| **Integrity** | **PASS.**<br>• Both manifests pass `sha256sum -c`: 484 top-level rows and 477 evidence rows.<br>• No duplicates, no leading `./`, neither manifest lists itself; each equals its tree exactly; the top level binds `evidence/SHA256SUMS`. |
| **Reproduction (C13)** | **PASS: 2/2.**<br>• `git am` on B6 with `COMMITS.tsv`'s committer data gives `479f6a88…` and **`4672ed30d036feb624ca84b4199af19d77f5768f`**, REPORT's head; 0 `gpgsig`.<br>• `src/` equals the head byte for byte. |
| **Scope** | **PASS.**<br>• `git diff --numstat bff0567b 4672ed30`: `PolyRatio.lean` +81/−15, `Asymptotic.lean` +121/−3, nothing else; each commit touches exactly one owned file.<br>• `git merge-tree --write-tree` with the records tip is clean: `c87eb403` and `a25338e0` both give `TCSlib` tree `6cfe46bf…`. |
| **Statements (C3), independently** | **PASS.**<br>• decls2 at the head: `PolyRatio.lean` **ADDED exactly `…GSW.Parameters.ofFamily_columns_le`**, 0 CHANGED, 0 REMOVED; `Asymptotic.lean` 0/0/0.<br>• **The helper's statement equals the brief's** fenced statement byte for byte, with only ` := by` added (`frozen/helper-statement.txt`).<br>• **Headers compared exactly:** all five targets have headers (4, 15, 16, 9 and 10 lines) and statement prose byte-identical to B6. |
| **`heff` kept** | **PASS.** A1 and A3 take `[hF, heff, hm]` at B6 and at the head, with `heff : ReductionEfficient F` and `heff : LeveledReductionEfficient F L` unchanged (`frozen/heff-check.txt`). No hypothesis removed or added; the proofs use `heff` through `reductionEfficient_iff` / `leveledReductionEfficient_iff`. `ReductionEfficient`, `LeveledReductionEfficient` and their readers are untouched (the frozen check). |
| **Frozen regions (C4), independently** | **PASS.** Restore-the-bodies check: each head normalizes **byte-identically** to B6 after the bodies go back to `sorry`, the refreshed sketches (G16, both G17) go back to B6's, the private glue `two_mul_width_lt_of_ratio` is deleted, the helper (10 lines with its docstring) is deleted, **after checking that it sits directly after `pBoot_eq` and directly before `### Targets G16–G17`**, its two-line *Main results* entry is deleted, and each "… are proved here." goes back to "… are admitted statement-phase targets.".<br>• 6 controls each FAIL (PolyRatio: header, definition body, *Main results* text; Asymptotic: `heff`'s type, module prose, deleted target). B6 against itself passes. |
| **Public declarations** | **PASS.** Exactly the one the brief names; the other new name is `private`. |
| **Admissions** | **PASS.**<br>• 0 `sorry`, `admit`, `native_decide`, `axiom` or `opaque` in the code; no new `set_option`, `attribute` or `@[simp]`; no import added.<br>• Base→head: 5 `sorry` → 0. Phase 2: admissions **37 in 14** = `base-sorries.txt` minus the five targets (the brief's C2 count). |
| **Axioms (C5)** | The worker's census: 37 constants; 32 standard, 5 through allowed names. **Phase 2 reproduces it** 37/37 with the same sets, and the traces name only allowed frozen targets of other units: G16 and the glue `[bootNoise_le]`; G17 pure `[bootNoise_le, decrypt_keygen_fheEvalCircuit]`; G17 leveled `[bootNoise_le, decrypt_keygen_leveledEvalCircuit]`; A3 `[distAdv_leveledView_le]`. **A1 `[propext, Classical.choice, Quot.sound]` and the helper `[propext, Quot.sound]`**, as required. No trace names a declaration of `PolyRatio.lean` or `Asymptotic.lean`. |
| **Rule 10 (C6)** | The worker: strict/coe A/B at head and base (16 probes, 0 errors) and pairs incl. the helper's. **Phase 2:** canonical coe-A and seal B, 0 errors, PolyRatio 1,394/1,395 and Asymptotic 1,653/1,654 requested and verified (the worker's coe counts exactly). My 4 liveness pairs, one for the helper, ALL_OK. **Own-definition seal:** `PolyRatio.lean` compiles with `Parameters.ofFamily` and `pBoot` irreducible from the helper on; its NEG control fails exactly once. Unfold scan: 0 definitions. |
| **Duplication** | **PASS** (below). Every must-reuse item used or rightly not needed. U1819-F01, F03 record the overlaps. |
| **Hygiene (C8, C9)** | **PASS.** PolyRatio 179 → 245 (max width 98), Asymptotic 340 → 458 (max width 99); +184 fill lines (under the 290–500 estimate: the frozen G12, L3, G13, L5 and phase 5's bound carry the analysis). The helper and the glue have formulas and "Glue."; G16 (23-line body), A1 (35) and A3 (85) have sketches and step comments. U1819-F02 on the unrefreshed sketches. |
| **Lint (C7)** | **PASS.** 92 FAIL / 103 WARN over 540 files at B6, at `4672ed30` and at the stack, identical line sets; `style_lint` 0 findings. |
| **Clashes (C10)** | **PASS.** `ofFamily_columns_le` and `two_mul_width_lt_of_ratio` occur in no `TCSlib/` or `audits/` file of the 346 local and remote-tracking heads. |
| **Build (C1)** | The worker reports a 224-module bootstrap and a 5-module head sweep. **Phase 2:** 6/6 rc 0 on B6 (with the root) and 12/12 stacked. |

## The proofs, target by target

- **Helper `Parameters.ofFamily_columns_le`** (`PolyRatio.lean:106`):
  `rw [Parameters.columns_eq, Parameters.ofFamily_lwe, Parameters.ofFamily_width]`, then
  `Nat.mul_le_mul_right _ (Nat.add_le_add_right (F.dimension_le κ) 1)`. The `Nat` form, as the brief states it
  (U18-U19-W1). Its docstring has the words, the formula and "Glue.".
- **G16 `bootRatio_le_poly`.** `hw` (`ofFamily_width`), `hm : m ≤ s(κ)` (`ofFamily_lwe`, `F.samples_le`), `hN` (the
  helper), `hlog : ⌈log₂ N⌉ ≤ N̂` (`Nat.clog_le_iff_le_pow` with `Nat.lt_two_pow_self`, then `hN`), G13 `bootNoise_le`
  at `β = m·B`; `pBoot_eq` and `PolyExpr.eval_mul/_pow/_add/_const`; a three-step `calc`: `gcongr` with G13, `ring`
  for `8·4^33·2 = 2^70`, `gcongr` with the bounds. The factor `8` and the constant `2^70` are Q-6B-W1 A's.
- **Private glue `two_mul_width_lt_of_ratio`:** from `hq` and `y ≤ bootNoise P (m·B)`,
  `2·(ℓ·y) < q/2`; G16, `Nat.mul_le_mul_left`, `modulus_ge_two`, `ofFamily_lwe`, `omega`. Used three times.
- **G17 pure:** G12 `decrypt_keygen_fheEvalCircuit` applied as stated, its condition from the glue.
- **G17 leveled:** `hin : m·B ≤ bootNoise P (m·B)` by `bootNoise_eq`, `N ≥ 1` (`Nat.pos_of_neZero`, the instance
  `Parameters.neZero_columns`) and `Nat.one_le_pow` (U1819-F01); then L3 `decrypt_keygen_leveledEvalCircuit` with the
  glue at `y = bootNoise P (m·B)` and at `y = m·B`.
- **A1 `indCPA_of_dlweAssumption`.** `reductionEfficient_iff` on `heff` at `false`, `true` gives `D₀`, `D₁`;
  `LWE.dlweAssumption_iff` makes their advantages negligible; `EnsembleLemmas.negligible_polyExpr_mul` (the
  `EnsemblesLemmas.lean:377` copy) with `negligible_two_pow_neg`; `Negligible.add` twice and `Negligible.mono`. At each
  `κ`: phase 5's `distAdv_encrypt_le_of_width` with `w = r(κ)` (`q ≤ 2^w` by `F.modulus_le_pow`, `hm` through
  `ofFamily_lwe`); `N·2^{−κ} ≤ N̂·2^{−κ}` from the helper; `distAdv ≥ 0` by `distAdv_def` and `abs_nonneg`;
  `linarith only`.
- **A3 `leveledINDCPA_of_dlweAssumption`.** `leveledReductionEfficient_iff` on `heff` at `false`, `true`; the majorant
  `(2·L·N̂ + 1)·(2·(adv D₀ + adv D₁) + N̂·2^{−κ})` as `negligible_polyExpr_mul` of an explicit `PolyExpr` applied to
  `((hneg₀.add hneg₁).const_mul 2).add hstat`. At each `κ`: L5 `distAdv_leveledView_le` at `(false, true)`;
  `Regev.two_extractionError_le`; each level pair `≤ 2·(a₀ + a₁) + 2·N·t` by `levelTerm_eq` and the four
  dominations; the double sum by `Finset.sum_le_sum` twice, `Finset.sum_const`, `Finset.card_univ`,
  `Fintype.card_fin`, `nsmul_eq_mul`; the challenge term by `challengeTerm_eq`; `aᵢ ≥ 0`; one `mul_le_mul` step with
  `N ≤ N̂` and `linarith only`. I checked the slack term the REPORT gives: it is nonnegative with `a₀, a₁, t ≥ 0`.

## Duplication sweep (binding)

- **`dup-sweep.md` §U18-U19 must-reuse list.**
  - **Used:** G12, G13, L3 (U14-U16) and L5 (U15-U17) as frozen statements; `Parameters.ofFamily_lwe`,
    `Parameters.ofFamily_width`, `Parameters.columns_eq`, `pBoot_eq`, `bootNoise_eq`, the instance
    `Parameters.neZero_columns`; `PolyExpr.eval_const/_add/_mul/_pow`; `distAdv_encrypt_le_of_width`,
    `Regev.two_extractionError_le`, `reductionEfficient_iff`, `leveledReductionEfficient_iff`, `levelTerm_eq`,
    `challengeTerm_eq`, `LWE.dlweAssumption_iff`, `EnsembleLemmas.negligible_polyExpr_mul`, `negligible_two_pow_neg`,
    `Negligible.add`, `.mono`, `.const_mul`; `Nat.clog_le_iff_le_pow`, `Nat.lt_two_pow_self`; `Nat.mul_le_mul` and
    `Nat.pow_le_pow_left` through `gcongr`; `Finset.sum_le_sum`, `Finset.sum_const`, `Finset.card_univ`,
    `Fintype.card_fin`.
  - **Not needed:** `PolyExpr.eval_var` (no `var` occurs); `LWE.Family.advantageAt_eq` (`advantageAt` is never opened).
  - **Precedent** `LWE.Family.encodeChallenge_length_le`: its pattern is the helper's proof; a different conclusion.
- **The "do not" list is respected.** `ofFamily`'s body is never read (seals, the own-definition seal, the unfold
  scan); no helper has an efficiency hypothesis; no `distAdv_nonneg` is added; neither of the two other
  `negligible_polyExpr_mul`s is used.
- **My searches** (`logs/searches-u1819.txt`; `exact?` probes with the use's hypotheses, G53-01). The probe ran **at
  B6** (a tree whose `PolyRatio`/`Asymptotic` oleans are B6's) and again at the head:
  - **E1, the helper's statement:** at B6 `exact?` fails, so no other lemma states it; at the head it finds
    `Parameters.ofFamily_columns_le` itself (positive control).
  - **E2** `Nat.clog 2 n ≤ n`: no lemma; Mathlib's 26 `clog` lemmas include no `clog_le_self`.
  - **E3** `β ≤ bootNoise P β`: no lemma; no `le_bootNoise`-style name (U1819-F01).
  - **E4** the glue's arithmetic core (`8·y < q`, `2 ≤ q` ⊢ `2·y < q/2`): no lemma (`omega`).
  - **E5** `0 ≤ distAdv X Y D`, **E6** `0 ≤ LWE.decisionAdvantage P χ D` (with the instances): no lemma;
    `distAdv_nonneg`, `decisionAdvantage_nonneg`, `advantageAt_nonneg` occur nowhere at B6.
  - **K3** (control) `n < 2 ^ n`: finds `Nat.lt_two_pow_self`.
- **Near relatives, as disclosed:** `Hashing/SIS/Asymptotic.lean`'s `negligible_collisions_of_SIS` (the same
  `Negligible` bookkeeping, nothing copied); EF-R2-R3's `singleBitSecure_of_dlweAssumption` (not landed; nothing
  reused); phase 5's inline `have hN` (U1819-F03).

## Findings

**Blockers: none. Majors: none. Minors: none.**

- **U1819-F01 (info; records side). `m·B ≤ bootNoise P (m·B)` is derived inline in two units.**
  - G17 leveled's `hin` (10 lines) and U14+U16's G12 `hle` (its delivery, not B6) prove the same fact from
    `bootNoise_eq` and `N ≥ 1`. G17 leveled's frozen sketch prescribes it, and no lemma exists (E3).
  - This is U1416-F01 (the pre-dispatch sweep missed a fact two units need), seen from this side. It is not a private
    helper copied across files: both are inline steps.
  - **Fix.** None to the delivery. The cleanup item of Q-U1416-2 A covers both sites (Q-U1819-2).
- **U1819-F02 (info). A1's and A3's frozen sketches were left as they were.**
  - A1's sketch says `hm` is read "through `Parameters.ofFamily_lwe` and `Parameters.ofFamily_width`" (the proof needs
    only `ofFamily_lwe`) and bounds `N` "(`dimension_le`, `PolyExpr.eval`)" (the proof cites the helper, which uses
    `dimension_le`). A3's sketch does not name `Negligible.const_mul`, the `Finset` counting lemmas or the helper.
  - The content is accurate, and COMMON §4 allows a target's sketch to stay. The G16/G17 sketches were refreshed.
  - **Fix.** None needed. Optional docs-only refresh later (Q-U1819-3 B).
- **U1819-F03 (info). Small inline repetitions, none a published lemma.**
  - The `hq`/`hmκ` blocks (7 lines) appear verbatim in A1 and A3 (same file).
  - A3's `hNε : 2·(N·ε) ≤ N·2^{−κ}` is the step inside phase 5's `distAdv_encrypt_le_of_width` (`have hN`,
    `GSW/Security.lean` at B6), which is not stated as a lemma and does not apply to `levelTerm`; disclosed.
  - `distAdv ≥ 0` (A1, A3) and `decisionAdvantage ≥ 0` (A3, twice) are inline `distAdv_def`/`decisionAdvantage_eq` with
    `abs_nonneg`, exactly as `dup-sweep.md` §0.5 prescribes; disclosed, with a promotion request (U18-U19-W2 (b)).

## Questions for Seyoon (recommended option first)

- **Q-U1819-1 · the helper's form (U18-U19-W1).**
  - **A (rec.)** Accept the `Nat` form, which is the brief's statement byte for byte. A1/A3 cast it with
    `exact_mod_cast`; the `PolyExpr` form would not shorten them, and EF-R1 is told to use this lemma.
  - **B** Restate it in the `PolyExpr` form. Not recommended: a re-delivery for no gain.
- **Q-U1819-2 · promotion requests (U18-U19-W2; U1819-F01, F03).**
  - **A (rec.)** Record both as cleanup items after the 6b fills land: (a) `le_bootNoise : β ≤ bootNoise P β` in
    `Bootstrap.lean`, used at G12 and G17 leveled (the same item as Q-U1416-2 A, one item for both sites); (b) a
    public `distAdv_nonneg` in `Foundations/Experiments.lean` with its `decisionAdvantage` corollary, as `dup-sweep.md`
    §0.5 foresees.
  - **B** Leave the inline steps as they are, with no cleanup item.
- **Q-U1819-3 · A1/A3 sketches (U1819-F02).**
  - **A (rec.)** Accept as delivered; no landing edit.
  - **B** A docs-only edit naming the helper and `Negligible.const_mul` in the two sketches, at landing or in a later
    docs pass.
- **Q-U1819-4 · landing order and EF-R1's base.**
  - **A (rec.)** Land after U14+U16, as the README orders (U18+U19 cites its G12, G13, L3), as delivered. EF-R1's base
    (Q-6BF-4 A, "plus U18-U19's accepted final if available") can now include `4672ed30`, so EF-R1 can cite the helper.
  - **B** Land it at once, before U14+U16. Possible (the files are disjoint and the traces stay allowed), but it gains
    nothing and departs from the README.

## Landing

- **Landing.** One PR with the two worker commits `479f6a88`, `4672ed30` on B6, as delivered (no landing edit).
  - **Prospective tree:** U18+U19 on the records tip, `TCSlib` tree `6cfe46bf55c7fa25387de44fd20474f01b6c91d0`
    (`git merge-tree --write-tree 4672ed30 <tip>` for both `c87eb403` and `a25338e0`); Lean-tested in phase 2 (P2-3).
  - With U14+U16 and U15+U17 as well, the full 6b stack, `TCSlib` tree `37ae0f32…`, is Lean-tested: 12/12, 0 `sorry`
    warnings, admissions 18 in 8, and all five targets standard-only (phase 2, P2-7).
- **Snapshot.** The replay trees were deleted; each rebuilds in about a minute.

## Evidence

`gsw-6b-u15-u17-u18-u19-final-r1-evidence.zip` sits beside this file; its SHA-256 is in `evidence-SHA256SUMS`. It is the
same zip as under `U15-U17/final-r1/`; its layout is in that review and in `PROVENANCE.txt`.
