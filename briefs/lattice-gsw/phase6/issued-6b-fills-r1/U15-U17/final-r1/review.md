# GSW 6b U15+U17 `gsw-6b-u15-u17` · final r1 · maintainer review (phase 1 static, phase 2 Lean replay)

**Verdict after phase 2: ACCEPT.** The three targets G15 (`GSW/Circular.lean`), L4 and L5 (`GSW/LeveledSecurity.lean`)
are proved as stated, sorry-free and standard-only. No public declaration was added. Phase 2 passed with no new finding.
One docs-only landing edit is recommended (Q-U1517-2 A); the delivery is also landable as it is (B). The details of
phase 2 are in [`phase2.md`](phase2.md).

- **Findings:** 0 blockers, 0 majors, 1 minor, 4 info.
  - The minor is form only: U1517-F02, three long private helpers have no step comments, and six of the seven helpers
    lack the "Glue." note or a Lean-order formula. The worker's own hygiene scan passed them.
  - The infos:
    - U1517-F01: the brief's and the sweep's `real_uniformKey_advantage` / per-seed hint cannot reach the frozen
      `levelTerm`; the worker's route is the right one (U15-U17-W1).
    - U1517-F03: `0 ≤ 2·(N·ε_LHL)` is read off the statistical bound at a constant test.
    - U1517-F04: an undisclosed near relative, phase 5's inline two-bit step.
    - U1517-F05: `LeveledSecurity.lean` is 681 lines, over the policy target 600 (under the 721 projected).
- **Phase 2 (2026-11-19, 01:36–02:21 UTC, both units of this review in sequence).**
  - **Build:** B6 + U15+U17: 7/7 rc 0, including the root `TCSlib`, admissions **39 in 14**. Stacked on the records tip
    (with U12/U13): 12/12 rc 0, admissions 30 in 12. The two owned oleans are byte-identical in both trees.
  - **Axioms:** all 67 stored constants of the two modules are standard, 0 `sorryAx`, in both trees; the same names and
    sets as the worker's census.
  - **Seals:** canonical coe-A and seal B, 0 errors: Circular 464/464, LeveledSecurity 1,561/1,562 requests verified.
  - **Controls:** 2 liveness pairs per owner, ALL_OK. **Unfold scan:** 0 foreign definitions.
  - **Lint:** unchanged. **Snapshot #11:** 0/0/0 before, mid-run and at the end.
  - **Extra:** the full 6b stack (records tip + U14+U16 + this unit + U18+U19) builds 12/12 with 0 `sorry` warnings,
    and every target of both units is standard-only there.

## What was reviewed

- **Delivery.** `inbox/fills/gsw-6b-u15-u17/` on `exchange/pass-shelat-ch5-8` at
  `4da71016e503c4f64ea2cee0ed2f6b748b1a32ec` (the origin tip when read). The final commit is `f501b6694` ("fill
  gsw-6b-u15-u17: final"); the folder is unchanged after it.
  - The checkpoint `2e6cddf0f` and the final are unsigned (0 `gpgsig`) and touch only `inbox/fills/gsw-6b-u15-u17/`.
  - Extracted with `git archive`: 473 files, namely `REPORT.md`, `SHA256SUMS`, 3 patches with `COMMITS.tsv`, `src/`
    (2 files) and `evidence/` (465 files).
- **Contract.** The issued pack at the records pin `27e53754`: `rulings.md` (Q-6BF-1..7, all A), `COMMON.md`,
  `U15-U17/brief.md`, `dup-sweep.md` (§0, §U15-U17), `targets.txt`, `base-sorries.txt`. Handoff §2 rules 10 and 15;
  `policy.md` §1–§3.
- **Rulings in force.** Q-6BF-2 A (this pairing) and Q-6BF-3 A (no public helper for this unit). Q-6B-W3 A (the
  μ-dependent `levelTerm` and the two-chain L5 bound) and P6-Q19 B (the reconstruction disclosure stays).
- **Base.** B6 = `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d`, tree `845bdc98…`. The records tip `c87eb403` (later
  `a25338e0`) has `TCSlib` tree `745bf4b4` = B6 + U12/U13 (#392): the Lean diff from B6 is `Branching.lean` and
  `DecryptFormula.lean` only.
- **Model for format and method:** `U12/final-r1/`, `U13/final-r1/` and Gate 53's G53-01 (duplication probes carry the
  use's hypotheses).
- **Tools.** Phase 1 used `git` and `python3 -I` only. Scratch work is under
  `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g6b-u1517-1819/`. Nothing was
  committed on any ref or pushed; the main checkout was only read, apart from this folder.

## Checks

| Check | Result |
|---|---|
| **Integrity** | **PASS.**<br>• Both manifests pass `sha256sum -c`: 472 top-level rows and 464 evidence rows.<br>• No duplicates, no leading `./`, and neither manifest lists itself.<br>• Each manifest equals its tree exactly; the top level binds `evidence/SHA256SUMS`. |
| **Reproduction (C13)** | **PASS: 3/3.**<br>• `git am` on B6 with `COMMITS.tsv`'s committer data gives `f4219a24…`, `56fe8e9a…` and **`619d202992b026ab7464595884d9b1b77736d8ab`**, REPORT's head; 0 `gpgsig`.<br>• `src/` equals the head byte for byte.<br>• Checkpoint 1's two patches have the same stable patch IDs as the final's first two; the final adds commit 3 (L5). |
| **Scope** | **PASS.**<br>• `git diff --numstat bff0567b 619d2029`: `Circular.lean` +21/−9, `LeveledSecurity.lean` +345/−26, nothing else.<br>• Each commit touches exactly one owned file.<br>• `git merge-tree --write-tree` with the records tip is clean: `c87eb403` and `a25338e0` both give `TCSlib` tree `611a86b4…`. |
| **Statements (C3), independently** | **PASS.**<br>• decls2 (records copy `fa81981a…`) at the head against B6: **0 ADDED, 0 CHANGED, 0 REMOVED**.<br>• Live control: making `leveledView_eq_levelHybrid` public gives 1 ADDED.<br>• **Headers compared exactly** (`frozen3.py`): G15, L4 and L5 have headers (7, 4 and 6 lines, keyword through `:= by`) and statement prose before `**Proof sketch.**` byte-identical to B6. |
| **Frozen regions (C4), independently** | **PASS.** Restore-the-bodies check: each head normalizes **byte-identically** to B6 after the bodies go back to `sorry`, the three refreshed sketches go back to B6's, the seven new `private` declarations (one `def`, six theorems) are deleted and "Both are proved here." goes back to "Both are admitted statement-phase targets." So no definition, reader, `set_option`, import, namespace or other text changed.<br>• 11 controls each FAIL (Circular: header, prose, definition body, reader, import, new public declaration; LeveledSecurity: header, prose, definition body, reader, the private `def` made public). B6 against itself passes. |
| **Public declarations** | **PASS.** None, as the brief requires. The seven new names are all `private`. |
| **Admissions** | **PASS.**<br>• 0 `sorry`, `admit`, `native_decide`, `axiom` or `opaque` in the code (comments stripped).<br>• No new `set_option`, `attribute` or `@[simp]`; no import added.<br>• Base→head: 3 `sorry` → 0. Phase 2: admissions **39 in 14** = `base-sorries.txt` minus G15, L4, L5 (the brief's C2 count). |
| **Axioms (C5)** | The worker's census: 67 constants, standard, `SORRY-REACHING 0`. **Phase 2 reproduces it:** 67/67 with the same names and the same sets; the targets `[propext, Classical.choice, Quot.sound]`; the `sorry` control is flagged. Identical in the stacked tree. |
| **Rule 10 (C6)** | The worker ran strict-A/B and coe-A/B at head and base (16 probes, 0 errors) and one liveness pair per owner. **Phase 2:** canonical coe-A and seal B, 0 errors, with Circular 464/464 and LeveledSecurity 1,561/1,562 requested and verified (the worker's coe counts exactly). My own 2 pairs per owner are ALL_OK. The explicit-unfold scan finds 0 foreign definitions (its 3 hits are the file's own private `levelPosHybrid`). |
| **Duplication** | **PASS** (below). Must-reuse items used, including **`acceptProb_fst`** (G15, L5); `acceptProb_snd` is not needed and nothing re-derives it. U1517-F01, F03, F04 record the overlaps. |
| **Hygiene (C8, C9)** | **Sizes PASS:** Circular 149 → 161 (max width 98), LeveledSecurity 362 → 681 (max width 100); +331 fill lines, in the brief's 290–490. **Form: U1517-F02** (step comments, helper formulas, "Glue."). The three targets' sketches are refreshed to the delivered proofs with prose untouched; L4 and L5 have step comments. |
| **Lint (C7)** | **PASS.** `campaign_style_lint --check8b`: 92 FAIL / 103 WARN over 540 files at B6, at `619d2029` and at the stack; identical FAIL/WARN line sets. The new INFO lines are the size lines and "681 lines > target 600" (U1517-F05). `style_lint` on the owned files: 0 findings. |
| **Clashes (C10)** | **PASS.** The seven new names occur in no `TCSlib/` or `audits/` file of any of the **346** distinct local and remote-tracking heads (`git grep -w`; positive control `levelReduction_eq` hits 4). All are private. |
| **Build (C1)** | The worker reports a 224-module bootstrap and a 6-module head sweep (root not built). **Phase 2:** 7/7 rc 0 on B6 (with root `TCSlib`) and 12/12 stacked on the records tip. |

## The proofs, target by target

- **G15 `distAdv_fheView_noEvk_le`** (14 lines).
  - The bijection `e : Seeds P χ ≃ (KeySeed P χ × Coins P) × (Fin N → Coins P)`,
    `(rg, R, R₀) ↦ ((rg, R₀), R)`, from `Equiv.prodCongr`, `Equiv.prodComm` and `Equiv.prodAssoc`.
  - Pointwise, the projected view is `realView P χ μ (e r).1`: `fheView_fst`, `fheView_snd`, `realView_eq`, `view_eq`,
    `Regev.keygen_fst`, then `rfl`, which only reduces the `Equiv` application and pair projections (the seals confirm
    that no TCSlib definition is read).
  - **`acceptProb_comp_equiv e`, then `acceptProb_fst`** drops `R`. `distAdv_def` and phase 5's `distAdv_encrypt_le`.
  - The statement stays over the projection of `fheView`; no restatement over `realView` is added (G45-01).
- **L4 `distAdv_levelHybrid_le`** (32 lines) with five private helpers.
  - **Position hybrids.** The private `def levelPosHybrid P χ L μ e t` is `H_{e+1}` with the first `t` ciphertexts of
    level key `e` replaced by encryptions of `0` (same coins). `levelPosHybrid_zero` (`G_0 = H_{e+1}`) and
    `levelPosHybrid_columns` (`G_N = H_e`, through `levelHybrid_eq` and `e + 1 ≤ e' ↔ e ≤ e'` for `e' ≠ e`).
  - **The chain.** `abs_sub_le_sum_hybrids`, `Fin.sum_univ_eq_sum_range`, `Finset.sum_le_sum`.
  - **Real key** (`acceptProb_sample_levelReduction`, 87-line body). One explicit seed bijection `Ψ` plants the LWE seed
    as the key seed of `pk_{e+1}` (`Function.update … e.succ`) and `R₀` at position `j`, keeping the replaced coordinates
    as a second factor; `uprob_comp_equiv Ψ` and `uprob_fst` reduce to a pointwise identity of views, read through
    `levelReduction_eq`, `reduction_eq`, `view_eq`, `hybridPlant_eq`, `levelAssemble_eq`, `levelMsgs_eq`,
    `levelHybrid_eq`, `levelKey_eq`, `evalKey_eq`, `Regev.keygen_fst`, with the cases `i < j`, `i = j`, `j < i`. The
    secret of `pk_{e+1}` is never read (top-down order), which is what makes the planting legitimate.
  - **Uniform key** (`abs_acceptProb_id_levelReduction_sub_le`). A regrouping `Φ` (`uprob_comp_equiv`, `uprob_prod`)
    writes each side as `uexp` over the reduction's own seeds `ω` of `acceptProb (uniformKeyView P m) (T ω)`, one test
    `T ω` for both sides; per `ω`, `uniformKey_uniform_advantage_le` twice and the triangle inequality give `2·(N·ε)`;
    `abs_uexp_sub_le` averages.
  - **One position:** two exact DLWE advantages (`LWE.decisionAdvantage_eq`, `distAdv_def`) plus the uniform-key gap,
    `abs_sub_le` twice, `linarith`, which is `levelTerm` (`levelTerm_eq`).
  - **Why not `real_uniformKey_advantage` or a per-seed bound:** U1517-F01.
- **L5 `distAdv_leveledView_le`** (32 lines) with two private helpers.
  - `leveledView_eq_levelHybrid`: `leveledView P χ L μ = levelHybrid P χ L μ L` (`leveledView_eq`, `levelHybrid_eq`,
    `not_le.mpr e.isLt`).
  - Each chain `H_0(μ) … H_L(μ)`: `abs_sub_le_sum_hybrids`, `Fin.sum_univ_eq_sum_range`, L4 at every level.
  - **Middle step** (`acceptProb_levelHybrid_zero_realView`): `challengeDist_eq` writes the distinguisher as `D` after a
    map of its own seeds; **`acceptProb_bind`** moves them into the sampler; a seed bijection plants `realView`'s key seed
    and challenge coins as those of `pk_0` and the challenge; **`acceptProb_comp_equiv`** and **`acceptProb_fst`** drop
    the replaced coordinates. Then phase 5's `distAdv_encrypt_le` on `challengeDist` and `challengeTerm_eq`.
  - `abs_sub_le` twice, `Finset.sum_add_distrib`, `linarith`. The two-chain bound is Q-6B-W3 A's.

## Duplication sweep (binding)

- **`dup-sweep.md` §U15-U17 must-reuse list.** Every item is used or rightly not needed:
  - **Used:** `distAdv_encrypt_le` (G15, L5); `uniformKey_uniform_advantage_le`, `reduction_eq`, `view_eq`,
    `realView_eq`, `uniformKeyView_eq`; `hybridPlant_eq` (through `levelReduction`); `abs_sub_le_sum_hybrids`;
    **`acceptProb_fst`** (G15, L5); `acceptProb_bind` (L5); `acceptProb_comp_equiv` (G15, L5); `uprob_fst`, `uprob_prod`,
    `uprob_comp_equiv` (L4's helpers, cited, not re-derived); `acceptProb_def`, `distAdv_def`;
    `LWE.decisionAdvantage_eq`; `Regev.keygen_fst`; the own readers `fheView_fst`/`_snd`, `leveledView_eq`,
    `levelHybrid_eq`, `levelMsgs_eq`, `levelAssemble_eq`, `levelReduction_eq`, `levelTerm_eq`, `challengeDist_eq`,
    `challengeTerm_eq`.
  - **Not needed, accepted:** `acceptProb_snd` (the dropped factor is always second, and no `prodComm`-then-`fst`
    pattern re-derives it); `exists_hybrid_gap` (the bound sums the gaps); `distAdv_comp`; `acceptProb_coins_fst`;
    `OneWay.uprob_update` (`Ψ` plants three coordinates at once); `fheView_eq`, `Seeds_eq`; the `simps` readers (the
    `_eq` readers rewrite whole applications); `exists_fixSeed` (not imported).
  - **Not applicable** (U1517-F01): `real_uniformKey_advantage`, `distAdv_multi_le_sum`, `distAdv_tuple_le_sum`.
- **The "do not" list is respected.** No `uprob_fst`-style marginalization is re-derived inline: G15 and L5 use
  `acceptProb_fst`, and L4's real-key helper applies `uprob_fst` itself (a must-reuse item) where the seeds are split
  between sampler and distinguisher. No restatement over `realView`.
- **My searches** (`logs/searches-u1517.txt`; `exact?` probes `runs/u1517-dup`, `runs/u1517-duplong`, each stated with the
  use's hypotheses and instances, G53-01):
  - **K2** (control): the averaging step finds `abs_uexp_sub_le`, the lemma used.
  - **D1** `0 ≤ Regev.extractionError P`: no lemma (`exact?` fails; no `extractionError_nonneg`-style name). U1517-F03.
  - **D2** `leveledView P χ L μ = levelHybrid P χ L μ L`: no lemma.
  - **D4** the uniform-key helper's statement: no lemma.
  - **K1** (the `acceptProb_fst` shape), **D3** (two bits under one uniform key) and **D5** (the `H_0`/`realView`
    identity) time out in `isDefEq`/`whnf` at 400k and again at 3.2M heartbeats, as the worker's P1/P3/P5 did. The name
    and shape searches decide them: `uniformKeyView` occurs only in `GSW/Security.lean` and `Regev/Experiments.lean`,
    where no statement takes two bits (the 14 two-bit hits are inside the proofs of the two `distAdv_encrypt_le`s,
    U1517-F04); `levelHybrid` occurs only in this file; `challengeDist` and `leveledView` only here and in
    `Asymptotic.lean`.
- **Near relatives.** As disclosed: `Symmetric.lean`'s `distAdv_symEncrypt_le` with its private
  `exists_equiv_symEncrypt`; Regev's `distAdv_encrypt_le`; `Hybrid.lean`'s private `acceptProb_plant` (plants one
  coordinate; `Ψ` plants three under a seed type that carries the key). Not disclosed: U1517-F04. None is restated or
  copied.

## Findings

**Blockers: none. Majors: none.**

- **U1517-F01 (info; pack hint, worker correct). The sweep's and the brief's L4 hints cannot reach the frozen bound.**
  - **The hints.** The brief and `dup-sweep.md` §U15-U17 suggest `real_uniformKey_advantage` and, as one option,
    `distAdv_multi_le_sum` per value of the other seeds (`exists_fixSeed`).
  - **Why they fail.** `levelReduction`'s planted message is `if b then levelMsgs P χ L e c.2.2.1 j' else false`: it
    reads the reduction's own coins `c` (B6 `LeveledSecurity.lean`, `levelReduction`). So `levelReduction` is not
    `reduction P μ D'` for a fixed `μ`. A per-seed bound would give `E_ω|real − uniform|`, while `levelTerm`'s DLWE terms
    are `|E_ω(real − uniform)|`, which can be smaller.
  - **What the worker did.** The brief's other option: `distAdv_multi_le_sum`'s proof followed with the seeds in the
    coins; the DLWE terms read through `LWE.decisionAdvantage_eq`; only the statistical gap averaged. Correct and
    minimal; disclosed (U15-U17-W1). The same kind of pack defect as U12-F02.
  - **Fix.** None to the delivery. Q-U1517-1.
- **U1517-F02 (minor; form, COMMON §5.4–§5.5, C9). Three long private helpers have no step comments; six helpers lack
  "Glue."; two lack a Lean-order formula.**
  - `acceptProb_sample_levelReduction` (87-line body), `abs_acceptProb_id_levelReduction_sub_le` (41) and
    `acceptProb_levelHybrid_zero_realView` (34) have sketches whose steps are visible (`let Ψ`, `have hsec`, the
    `rcases` on positions) but **no step comment**.
  - `levelPosHybrid_zero` ("`G_0` is `H_{e+1}`: no position is replaced.") and `levelPosHybrid_columns` state the fact
    only in the paper's notation, without the formula in Lean order.
  - Only `levelPosHybrid` says it is glue ("glue for L4"); the other six helpers have no "Glue." note.
  - The REPORT's C9 says "every new private helper has a formula … the long proofs carry step comments. flagged = 0";
    its scan accepted "formula or Glue" and did not count step comments in helpers.
  - **No correctness impact.** The statements, proofs and sketches are right.
  - **Fix.** A docs-only landing edit, `proposed/LE-u1517-doc.diff` in the evidence (28 changed or added lines in
    `LeveledSecurity.lean`): "Glue." and the Lean-order formula on the seven helpers, and step comments in the three long
    ones. The code with comments and docstrings stripped is identical, the frozen check still passes, the maximum width
    is 100, and the hygiene scan is clean. It is not replayed; a landing replay would cover it. Q-U1517-2.
- **U1517-F03 (info). `0 ≤ 2·(N·ε_LHL)` from the statistical bound at a constant test.**
  - `hc` in the uniform-key helper applies `uniformKey_uniform_advantage_le` to `fun _ _ => true` and `abs_nonneg`.
  - The direct route is `Regev.extractionError_eq` with `Real.sqrt_nonneg`; neither is a lemma that this re-proves (D1:
    no `extractionError` nonnegativity lemma exists). Correct, 5 lines, not a duplication. No change needed.
- **U1517-F04 (info; disclosure). An undisclosed near relative.**
  - The per-seed step of `abs_acceptProb_id_levelReduction_sub_le` (two `uniformKey_uniform_advantage_le` and the
    triangle inequality through the uniform view) is the same step as the inline `hstat₀`/`hstat₁`/`htriangle` of
    phase 5's `distAdv_encrypt_le` proof (`GSW/Security.lean:262–276` at B6) and of Regev's
    (`Regev/Experiments.lean:314–325`).
  - Neither is a stated lemma, so nothing public is re-proved; but REPORT §6's near-relative table omits it
    (disclosure is required, COMMON §5.2).
  - **Fix.** None to the source. Recorded here.
- **U1517-F05 (info). `LeveledSecurity.lean` is 681 lines,** over the policy target 600 (lint INFO), under the 721
  projected for it (G6B-F07) and the 1,000 cap. No action; a later split would be a cleanup item.

## Questions for Seyoon (recommended option first)

- **Q-U1517-1 · L4's route (U15-U17-W1; U1517-F01).**
  - **A (rec.)** Accept it as delivered: the brief's other option, `distAdv_multi_le_sum`'s proof followed with the seeds
    in the coins. The pack's hint is noted here as inapplicable; the issued pack stays as pinned.
  - **B** As A, and also amend `dup-sweep.md` §U15-U17's wording in place. Not recommended: issued packs are pinned
    records, and this review carries the correction (as Q-U12-2).
- **Q-U1517-2 · helper docstrings and step comments (U1517-F02).**
  - **A (rec.)** Land with the docs-only landing edit `LE-u1517-doc` (evidence `proposed/LE-u1517-doc.diff`), one extra
    commit on `LeveledSecurity.lean`, and replay the landing head once (7 modules, about a minute) before the PR. It
    pre-empts the same point at the fill gate.
  - **B** Land as delivered and leave the form points to a later docs sweep. Acceptable: the proofs and statements are
    unaffected.
  - **C** Ask the worker for a revision. Not recommended: a re-delivery for comments only.

## Landing

- **Landing.** One PR with the three worker commits `f4219a24`, `56fe8e9a`, `619d2029` on B6, plus `LE-u1517-doc` under
  Q-U1517-2 A.
  - The README's order puts U15-U17 first among U14–U19; it is disjoint in files from U14+U16 and U18+U19 and lands in
    any order with them. Its targets end sorry-free whatever lands before it.
  - **Prospective tree:** U15+U17 on the records tip, `TCSlib` tree `611a86b4cbcef82ed2e2fa04b9d7ba9b4f487542`
    (`git merge-tree --write-tree 619d2029 <tip>` for both `c87eb403` and `a25338e0`); Lean-tested in phase 2 (P2-3).
  - With U14+U16 and U18+U19 as well, the full 6b stack (`TCSlib` tree `37ae0f32…`) is Lean-tested too: 12/12, 0
    `sorry` warnings, admissions 18 in 8 (phase 2, P2-7).
- **Snapshot.** The replay trees were deleted; each rebuilds in about a minute. Snapshot #12 can be adopted from a fresh
  replay of whatever merges.

## Evidence

`gsw-6b-u15-u17-u18-u19-final-r1-evidence.zip` sits beside this file; its SHA-256 is in `evidence-SHA256SUMS`. The same
zip is filed under `U18-U19/final-r1/`.

- It holds `PROVENANCE.txt` and an inner `SHA256SUMS` (475 files), which does not list itself.
- It contains the integrity, reproduction, merge-tree and stack-head logs, decls2, the frozen check with its controls,
  the static and hygiene scans, the B6, stacked and full-stack replays, the axiom censuses, the collectors, the coe-A
  and seal-B records with their sealed copies and raw logs, the controls, the duplication probes and searches, the
  unfold scans, lint, the proposed landing edit, and every tool and probe source.
