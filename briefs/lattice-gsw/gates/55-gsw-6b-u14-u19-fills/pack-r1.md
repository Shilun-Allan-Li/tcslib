# Gate 55 · the GSW 6b fills gate for U14+U16, U15+U17 and U18+U19: PR #396 · round 1

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). This is **Gate 55**,
the fills gate for the last three GSW phase-6b fill units: the proofs of fifteen 6b targets that #377 stated and Gate 46
cleared, and the two public glue lemmas that ruling Q-6BF-3 (A) allows. One draft PR is audited. It carries the three
units' worker commits and two docs-only maintainer landing edits (6b fill rulings, Seyoon, 2026-11-19).

- **PR #396**, branch `land/gsw-6b-u14-u19`, head **`dd6d274eba9b55b5a2c7c97730245a4f1bea1e90`** (tree
  `c33c231aaaea24f45b62b0c848cb4d3af59ef536`, `TCSlib` tree **`004dfaefe57ac8d72d539c55151ccf0fce0b6b65`**), base
  `cryptography/pass-shelat-ch2-4`. Its merge base with the records tip is the records tip at staging,
  **`53e430b68cbe22416312a4f80bbc3426c71cf86d`**: the branch was cut from it. Nine SSH-signed commits; 6 files, +883/−90.
- **B6** = `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d`, the #377 merge and olean snapshot #11's T (`TCSlib` tree
  `949dfd63c2539e1ccd738ab96ec424ee6cb17798`). **The frozen statements are B6's.** The records tip carries U12/U13
  (#392, merged as `0ab20424`; `TCSlib` tree `745bf4b4`): against B6 its Lean differs only in `GSW/Branching.lean` and
  `GSW/DecryptFormula.lean`. The six files of this PR are blob-identical at B6 and at the records tip
  (`staging-checks-r1.txt` §2, §5).
- **The fills head** `103a8bde9aa19e933633fa70eee94e75a308806b` is the last worker commit on the branch. Its `TCSlib`
  tree `37ae0f3223db419f636bb2d39484191f698de994` equals that of the full 6b stack that the U15-U17/U18-U19 review
  replayed (`6e363a298ff6fe59e861f968d4c54262d96e9f74`, on no ref). The two landing edits follow it.
- **Records pin:** the commit that files this directory, `briefs/lattice-gsw/gates/55-gsw-6b-u14-u19-fills/`.
  `dispatch-r1.md` and the prompt name it. Its ancestry from the records tip at staging, `53e430b6` ("Records: 6b
  fill landing rulings; ledger DL-71"), adds this directory, the landing record `ISSUED/landing-u14-u19.md`, the PR
  number and, at most, decision-log rows, so every record this pack cites reads the same at `53e430b6` and at the pin
  (`source-head-r1.json` `records_sha256_at_staging_tip`; the decision log is cited by row, not by hash).
- **Mathlib** `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, **Batteries** `39260e31b7b3f7f05643da95242463b462dc05f1`
  (`lake-manifest.json` at the head), toolchain `leanprover/lean4:v4.25.0`.

Paths below are under `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/` unless they start with `TCSlib/` or
`briefs/`. `ISSUED/` is `briefs/lattice-gsw/phase6/issued-6b-fills-r1/`. Line numbers are at the head.

## How this gate runs (standing rules 17 and 18)

- **Cloud, reading only.** Every input is in the repository: the records branch at the pin, the PR branch, and the
  exchange branch at the delivery commits. Nothing is needed from Seyoon's machine.
- **No Lean replay, no cache.** The auditor does not run `lean`, `lake` or `lake exe cache get`, and builds nothing.
  The maintainer replayed in house: the three units' reviews (phase 2 on copies of snapshot #11, each unit on B6 and
  stacked on the records tip, plus the full 6b stack) and a **landing re-check of this PR's head**
  (`landing-u14-u19-recheck-evidence.zip` in this directory). Those replays are the gate's build evidence; the audit
  grades them by reading the evidence ZIPs, their logs and their probe sources.
- Python as `python3 -I`; `git`, `sha256sum`, `unzip` and reading tools only. Mathlib/Batteries source may be read at
  the pinned revisions (GitHub, or a blob-filtered fetch), never built.

## Scope

| Unit | Files | Targets (head line) | Commits on the PR | What changes |
|---|---|---|---|---|
| **U14+U16** `gsw-6b-u14-u16` | `Bootstrap.lean`, `Leveled.lean` | G9 `encrypts_bootNAND` (`Bootstrap.lean:237`), G10 `decrypt_fheEval` (`:329`), G18 `decrypt_fheEvalCircuit` (`:381`), G12 `decrypt_keygen_fheEvalCircuit` (`:423`), G13 `bootNoise_le` (`:490`); L2 `encrypts_leveledEval` (`Leveled.lean:244`), L3 `decrypt_keygen_leveledEvalCircuit` (`:337`) | `7fc78336261434830042072fc360b9d804ebbeea` (Bootstrap), `96e22a6dbfa127c6730fabe7691c1f6b76ac87c7` (Leveled) | 7 proof bodies; the **public** helper `encrypts_bootGate` (`Bootstrap.lean:270`, directly after G9, with two `## Main results` lines); the **private** `four_pow_clog_le` (`:460`); sketches of G10, G13, L2 refreshed; two module admission sentences; Bootstrap 349 → 518 lines, Leveled 291 → 384 |
| **U15+U17** `gsw-6b-u15-u17` | `Circular.lean`, `LeveledSecurity.lean` | G15 `distAdv_fheView_noEvk_le` (`Circular.lean:139`); L4 `distAdv_levelHybrid_le` (`LeveledSecurity.lean:599`), L5 `distAdv_leveledView_le` (`:658`) | `a8f241819b8f32778ffc214ef9034634acd90b36` (G15), `f400635c569a6b4595bc8e2b4f67bf1f4f6bfa1b` (L4), `1664c477eee920490863d65e1667612feb4f4f98` (L5) | 3 proof bodies; **no public declaration**; seven **private** helpers in `LeveledSecurity.lean`: `def levelPosHybrid` (`:308`), `levelPosHybrid_zero` (`:318`), `levelPosHybrid_columns` (`:326`), `acceptProb_sample_levelReduction` (`:352`), `abs_acceptProb_id_levelReduction_sub_le` (`:457`), `leveledView_eq_levelHybrid` (`:510`), `acceptProb_levelHybrid_zero_realView` (`:528`); three sketches refreshed; one module sentence; Circular 149 → 161, LeveledSecurity 362 → 681 |
| **U18+U19** `gsw-6b-u18-u19` | `PolyRatio.lean`, `Asymptotic.lean` | G16 `bootRatio_le_poly` (`PolyRatio.lean:126`), G17 `decrypt_fheEval_of_ratio` (`:184`) and `decrypt_leveledEval_of_ratio` (`:214`); A1 `indCPA_of_dlweAssumption` (`Asymptotic.lean:297`), A3 `leveledINDCPA_of_dlweAssumption` (`:362`) | `f66fb1bb5d20c03dd0a37a3af651a5fe4929d6e1` (PolyRatio), `103a8bde9aa19e933633fa70eee94e75a308806b` (Asymptotic) | 5 proof bodies; the **public** helper `Parameters.ofFamily_columns_le` (`PolyRatio.lean:106`, directly after `pBoot_eq`, with two `## Main results` lines); the **private** `two_mul_width_lt_of_ratio` (`:158`); sketches of G16 and both G17 refreshed; two module sentences; PolyRatio 179 → 245, Asymptotic 340 → 458 |
| **Landing edits** (maintainer, docs only) | `LeveledSecurity.lean`, `Asymptotic.lean` | none | `64ccd270825a2f41f99bfbd3d95a6509c1f55b96` **LE-u1517-doc**, `dd6d274eba9b55b5a2c7c97730245a4f1bea1e90` **LE-u1819-doc** | LE-u1517-doc: "Glue." on the seven private helpers, Lean-order formulas on three of them, step comments in the three long ones (+22/−6; LeveledSecurity 681 → 697). LE-u1819-doc: A1's and A3's proof sketches name `Parameters.ofFamily_columns_le` where the proofs use it, instead of `Parameters.ofFamily_width`/`dimension_le` (+8/−8). |

- **The worker commits are the workers' patches.** The maintainer applied the delivered patches with
  `git am -3 -S --committer-date-is-author-date` on `53e430b6`, in the order U14+U16, U15+U17, U18+U19, keeping the
  workers' author and committer data. `git patch-id --stable` of each of the seven worker commits equals that of its
  delivered patch (7/7), and the six files at the fills head are blob-identical to the delivered `src/` and to the review
  evidence's `frozen/*.head.lean` (`staging-checks-r1.txt` §4–§5). The workers' own commits (`e09ce698`, `9852429e`;
  `f4219a24`, `56fe8e9a`, `619d2029`; `479f6a88`, `4672ed30`) are unsigned and on no ref; they exist only as the
  patches and as the reviews' reproductions on B6.
- **The landing edits** are the maintainer's. LE-u1517-doc is the review's `proposed/LE-u1517-doc.diff` applied as
  prepared: `LeveledSecurity.lean` at the head is blob-identical to the evidence's
  `proposed/LeveledSecurity.LE-u1517-doc.lean` (`bf70162b`). LE-u1819-doc was written at landing. With comments and
  docstrings stripped (and blank lines dropped), the code of all six files is identical at the fills head and at the
  PR head (`staging-checks-r1.txt` §4, with a negative control).
- **Deliveries** (exchange `exchange/pass-shelat-ch5-8`, tip at staging `8f15c31d38b834505dc3ecd64200dc524eeacccc`;
  each folder is unchanged since its final):
  - U14+U16 `inbox/fills/gsw-6b-u14-u16/`: checkpoint `e727c64dd02c0219f6f4c4588638ebea946d14cc`, final
    `90b4c3a1549008f93ae35a0395bca88f0f557f73` (read by its review at exchange `b614ee77`);
  - U15+U17 `inbox/fills/gsw-6b-u15-u17/`: checkpoint `2e6cddf0f0a477e29b50a866bc587331c43c1ad2`, final
    `f501b6694a82f7c57a82c18da7985b38ed9ca5ca` (read at `4da71016`);
  - U18+U19 `inbox/fills/gsw-6b-u18-u19/`: checkpoint `5fb0d4b8324f1c5e8d1e64e013f083f0bd154e20`, final
    `c414248e3562acfb91ac05cab16e6e308f56ee26` (read at `4da71016`).
  - Each has `REPORT.md`, `SHA256SUMS`, `patches/` with `COMMITS.tsv`, `src/` and `evidence/`.
- **Issued pack:** `ISSUED/` at its pin for U14-U19, `27e53754d28703907571cacbaf905b441e03c393` (`rulings.md`,
  `README.md`, `COMMON.md`, the three `brief.md`s, `dup-sweep.md` §0 and §U14-U16/§U15-U17/§U18-U19, `targets.txt`,
  `closures.txt`, `base-sorries.txt`). Since that pin only the three U14–U19 dispatch prompts changed (`f5dade19`, the
  pin hash filled in; 4 lines each), outside the units' `final-r1/` review folders.

**Out of scope** (mention only if something in scope depends on it):
- The 6b **statements** (#377, Gate 46 CLEAR, merged at B6): their fidelity to the sources is settled. They are the
  **base** of question B, not an audit item.
- U12 and U13 (#392, Gate 53 CLEAR, merged), EF-R1 and its base (Q-6BF-4), and A1/A3's `heff` hypotheses as such
  (Q-6BF-1 A: they stay; EF-R1 discharges them later).
- Rule 15 beyond this PR: the fills prove correctness, noise bounds and security reductions; no target is an efficiency
  claim (COMMON §6). Check only that the PR adds no hypothesis and no helper whose hypothesis is an efficiency claim.
- The DL-71 cleanup itself (publishing `le_bootNoise`, `LWE.sample_eq`, `distAdv_nonneg` after the fills land).
- The merge conditions: the snapshot #12 adoption (a replay of whatever merges) and the merge itself.

## Rulings and records in force

1. **The issued rulings** `ISSUED/rulings.md` (Q-6BF-1..7, all A, Seyoon 2026-11-18/19), in particular:
   **Q-6BF-1 A** (A1 and A3 are filled **from their frozen `heff` hypotheses**; `Asymptotic.lean`'s statements do not
   change; EF-R1 is a separate unit), **Q-6BF-2 A** (this grouping) and **Q-6BF-3 A** (**exactly two** public glue
   lemmas, `encrypts_bootGate` in `Bootstrap.lean` and `Parameters.ofFamily_columns_le` in `PolyRatio.lean`, pure
   insertions, decls2 ADDED = 1 each, each sealed with its own controls; any other new public declaration is E-SCOPE).
2. **6b fill rulings (Seyoon, 2026-11-19)**, decision log `LatticeCryptographyPlan.md`, row "6b fill rulings
   (Seyoon)":
   - **Landing:** one PR with the three units' worker commits; the routes are accepted as delivered (**Q-U1517-1 A**:
     L4's route, U1517-F01); one Codex fills gate (this one). This supersedes Q-U1416-3 and Q-U1819-4 (landing order).
   - **Docs: fix both.** **LE-u1517-doc** (U1517-F02: step comments, "Glue." notes, formula docstrings on U15+U17's
     helpers; Q-U1517-2's option A edit) and a docs-only refresh of U18+U19's A1/A3 sketches, **LE-u1819-doc**
     (U1819-F02; Q-U1819-3's option B edit, made at landing); one replay (the landing re-check).
   - **Duplicates:** the inline copies are accepted and recorded as **ledger DL-71**
     (`briefs/pass-shelat-ch5-8/duplication-ledger.md`): `m·B ≤ bootNoise P (m·B)` (G12's `hle`, G17 leveled's `hin`),
     the `Prod.ext` of `LWE.sample_fst/_snd` (G12's `hs`), and nonnegativity of `distAdv` (A1, A3); publish
     `le_bootNoise`, `LWE.sample_eq`, `distAdv_nonneg` after the fills land (Q-U1416-1/2 A, Q-U1819-2 A). **Do not
     raise these three as findings against the PR**; check that DL-71 describes them and that nothing else is copied.
   - **Q-U1819-1 A:** `Parameters.ofFamily_columns_le` keeps its `Nat` form (the brief's statement byte for byte).
3. **Rulings the reviews list as in force** (each review's "Rulings in force"): Q-6B-W1 A (G16's factor `8` and the
   constant exactly `2^70`), Q-6B-W3 A (the μ-dependent `levelTerm` and L5's two-chain bound), P6-Q19 B (the
   reconstruction disclosure stays), the efficiency ruling Q2 A (A1/A3 statements kept), Gate 46's type-level Rule 10
   on `ofFamily`; plus the phase-6 rulings `briefs/lattice-gsw/phase6/rulings.md` and plan section r3
   `briefs/lattice-gsw/phase6/plan-section.md`.
4. **Fill rules:** `ISSUED/COMMON.md` §4 (what a fill may change; the frozen regions), §5 (Rule 10, duplication, hosts
   first, attribution, form), §6 (Rule 15); the unit briefs' targets, routes, must-reuse lists and unit checks.
5. **Duplication** (policy §1; precedents G44-01, G48-01, G45-01, GF-F01, S1/DL-61): disclosure is not acceptance; an
   undisclosed or unaccepted re-proof of a public TCSlib or Mathlib lemma, including an inline re-derivation, is a
   **major**. DL-71 is the acceptance for its three facts (item 2).
6. **Gate 53's lesson G53-01** (`gates/53-gsw-6b-u12-u13-fills/findings-r1.md`, `closure.md`): a duplication probe
   must carry the hypotheses and instances of the use it stands for; an `exact?` failure on a statement that is false
   without them does not show that no lemma exists. The three reviews state that their probes carry the use's
   hypotheses (U14-U16 D1–D7, U15-U17 D1–D5 and K1–K2, U18-U19 E1–E6 and K3). **Check that they do**, and hold your
   own probes and searches to the same rule.
7. **Rule 10** (policy §1, COMMON §5.1): other files' definitions are read only through published readers and lemmas;
   core/Mathlib definitions may reduce in `rfl`/`decide`/`show` steps; canonical coe-A seals are the check.
8. **Policy** (`policy.md`): attribution (tags or "Glue."), formula docstrings, a `**Proof sketch.**` for every proof of
   about 20 lines or more, width ≤ 100, files 150–600 target and < 1,000.
9. **Standing rules** `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2 (3, 5, 15, 17, 18).

## Questions for the audit

**A. Correctness of the proofs (fifteen targets, two public helpers, the private glue).** Read each proof against its
frozen statement. Does it establish the statement as stated, for every parameter (no special case through an instance,
a `decide` or an `omega` that does not cover the statement)? Is every helper true as stated and used as its docstring
says? The reviews' "The proofs, target by target" sections give the routes; check them, do not take them.
- **G9** `encrypts_bootNAND`: `bootNAND_eq`, G3 `encrypts_homEvalFormula` on `nandFormula`, fan-in by G8
  `maxFanin_nandFormula_le`, message by G7 `nandFormula_eval`, noise by `bootNoise_eq` and G8 `depth_nandFormula_le`.
- **`encrypts_bootGate`** (public): the case split `[]`, `[a]`, `a :: b :: l` through the frozen readers
  `bootGate_of_args_eq_nil`/`_singleton`/`_cons_cons`; `hG` (the padded gadget decrypts to `true` at noise `0`); the
  length bound from `DAGGate.isNAND_iff`. Is the brief's statement byte for byte the one at `:270`, and is it
  strong enough for both G10 and L2 without an unstated condition?
- **G10** `decrypt_fheEval`: the host `runWith_rel` (H19) with the relation
  "`Encrypts P t b.toNat (if v < k then βin else bootNoise P βk) C`"; the input block; acyclicity by `Cc.args_lt`; the
  gate step through `encrypts_bootGate`; the output through `fheEval_eq`, `Cc.eval_eq`, `Cc.values_eq`.
- **G18**, **G12**: G18 by `toNANDForm_eval`/`toNANDForm_isNANDForm` and G10; G12's honest key (`hs`, DL-71),
  `encrypts_evalKey`, `encrypts_keygen_encrypt`, `hle : m·B ≤ bootNoise P (m·B)` (DL-71).
- **G13** `bootNoise_le`: the exponent bound `9a + 2b + 22` from `decDepth_le`; the split `4^22·(4^a)^9·(4^b)^2`;
  the private `four_pow_clog_le` (`1 ≤ y → 4^⌈log₂ y⌉ ≤ 4·y²`); constants `c₀ = 33`, `c₁ = 9`, `c₂ = 2` as frozen;
  `N ≥ 1` by the instance (the old sketch's `N = 0` case dropped).
- **L2** `encrypts_leveledEval`: the dependent relation
  "`∀ hv : depthAt v < L + 1, Encrypts P (t_{depthAt v}) b.toNat (max βin (bootNoise P βk)) C`"; level arithmetic
  (`depthAt_gate`, `levelGate_of_lt` at `δ − 1 < L`, `hsucc`); gates above `L` excluded by the relation. Is anything
  above level `L` silently assumed?
- **L3** `decrypt_keygen_leveledEvalCircuit`: the literal ciphertexts by `Fin.addCases` (the NOT literal by
  `Encrypts.sub` of `encrypts_gadget`, message `(!b).toNat = 1 − b.toNat`, noise `0 + m·B`); L2 on
  `(Cc.toNANDForm hC).layerNAND`; L1 for the keys.
- **G15** `distAdv_fheView_noEvk_le`: the seed bijection `e` and the pointwise `rfl` (only the `Equiv` application and
  pair projections reduce); `acceptProb_comp_equiv`, `acceptProb_fst`; phase 5's `distAdv_encrypt_le`.
- **L4** `distAdv_levelHybrid_le` with the five private helpers: the position hybrids `G_t`
  (`levelPosHybrid`), `G_0 = H_{e+1}`, `G_N = H_e`; the real-key helper's seed bijection `Ψ` (87-line body; is the
  secret of `pk_{e+1}` really never read, so that planting the LWE seed is legitimate?); the uniform-key helper's
  averaging (`abs_uexp_sub_le`) and `hc : 0 ≤ 2·(N·ε)` (U1517-F03); the sum against the frozen `levelTerm` (U1517-F01:
  why the brief's per-seed hint would not reach it).
- **L5** `distAdv_leveledView_le`: `leveledView = levelHybrid … L`; the two chains `H_0(μ) … H_L(μ)` with L4 at every
  level; the middle step `acceptProb_levelHybrid_zero_realView` (`challengeDist_eq`, `acceptProb_bind`, a seed
  bijection, `acceptProb_comp_equiv`, `acceptProb_fst`); the two-chain bound of Q-6B-W3 A.
- **`Parameters.ofFamily_columns_le`** (public): `columns_eq`, `ofFamily_lwe`, `ofFamily_width`, `F.dimension_le`;
  no read of `ofFamily`'s body.
- **G16** `bootRatio_le_poly`: `hw`, `hm`, `hN` (the helper), `hlog : ⌈log₂ N⌉ ≤ N̂`, G13 at `β = m·B`; `pBoot_eq`; the
  three-step `calc` (`8·4^33·2 = 2^70`). **G17** pure and leveled: the private `two_mul_width_lt_of_ratio`
  (`2·(ℓ·y) < q/2` from `hq` and `y ≤ bootNoise P (m·B)`), then G12 and L3; G17 leveled's `hin` (DL-71).
- **A1**, **A3** (from `heff`): `reductionEfficient_iff`/`leveledReductionEfficient_iff` at `false`, `true`;
  `dlweAssumption_iff`; `EnsembleLemmas.negligible_polyExpr_mul` with `negligible_two_pow_neg`; `Negligible.add`,
  `.const_mul`, `.mono`; at each `κ` phase 5's `distAdv_encrypt_le_of_width` (A1) or L5 with
  `Regev.two_extractionError_le` and `levelTerm_eq`/`challengeTerm_eq` (A3); `N ≤ N̂` by the helper. Is A3's final
  `linarith only` step sound (the review checked the slack term is nonnegative with `a₀, a₁, t ≥ 0`)?
- **Axioms** (maintainer evidence, not re-run): in the landing re-check, all 15 targets and `encrypts_bootGate`
  `[propext, Classical.choice, Quot.sound]`, `Parameters.ofFamily_columns_le` `[propext, Quot.sound]`; 168 stored
  constants of the six modules, 0 `sorryAx`; a `sorry` control flagged. In the reviews' B6 runs some targets reach
  `sorryAx` only through other units' then-admitted targets; on the full stack and at the head none does. Is the census
  consistent with the proofs you read?

**B. Frozen-statement fidelity.** Against B6 (`git show bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d:<path>`; the six files
are the same blobs at the records tip):
- Is every target header (keyword through `:= by`) and its statement prose before `**Proof sketch.**`
  byte-identical? (`staging-checks-r1.txt` §6: 15/15 the same, header lengths 3–16 lines.) Is every definition, reader,
  instance, `import`, `set_option`, namespace and `variable` line unchanged? The staging classified every removed line
  of the PR diff (§6): 15 `sorry` bodies, 5 module admission sentences, and sketch-paragraph lines of 11 targets (G10,
  G13, L2, G15, L4, L5, G16, both G17, A1, A3). The reviews' restore-the-bodies normalizations reproduced B6 byte for
  byte for each unit, with controls (evidence `frozen/`).
- Are the refreshed sketches (the workers' for G10, G13, L2, G15, L4, L5, G16, G17; **LE-u1819-doc's** for A1, A3)
  accurate descriptions of the delivered proofs, and are the kept sketches (G9, G18, G12, L3) still accurate?
- Are the new module sentences true at the head, and are they the permitted admission-sentence edits of COMMON §4?
- Are the two public helpers pure insertions at the briefed places (`encrypts_bootGate` directly after G9 and before
  G10; `Parameters.ofFamily_columns_le` directly after `pBoot_eq` and before `### Targets G16–G17`), each with its two
  `## Main results` lines, not `@[simp]`? Are all other new declarations `private`, placed before first use, not
  `@[simp]`? (decls2 against the records tip: ADDED exactly the two helpers, 0 CHANGED, 0 REMOVED; U15-U17's live control,
  one private helper made public, gives 1 ADDED.)

**C. Scope and integrity.** Does the PR change exactly the six owned files and nothing else (no 6a, phase-5, LWE,
facade, `blueprint/` or `audits/` file; no U12/U13 file)? Do the seven worker commits equal the delivered patches and the
fills head's files the delivered `src/` (`staging-checks-r1.txt` §3–§5)? Is the fills head's `TCSlib` tree the reviewed
full stack's (`37ae0f32`)? Are the two landing edits docs only: does stripping comments and docstrings give identical
code (§4), and does LE-u1517-doc equal the review's prepared diff?

**D. The rulings.** Do A1 and A3 keep `heff` (headers byte-identical; Q-6BF-1 A) and use it only through
`reductionEfficient_iff`/`leveledReductionEfficient_iff`? Are exactly the two Q-6BF-3 helpers public, with the briefs'
statements byte for byte, and `ofFamily_columns_le` in its `Nat` form (Q-U1819-1 A)? Is L4's route the one ruled
acceptable (Q-U1517-1 A)? Do LE-u1517-doc and LE-u1819-doc do what the 6b fill rulings asked, and nothing more? Is
G16's constant exactly Q-6B-W1 A's, and L5's bound Q-6B-W3 A's? Does any choice of a worker or of the landing depend
on an unrecorded ruling?

**E. Duplication** (binding; items 2, 5 and 6 of the rulings above).
- `ISSUED/dup-sweep.md` §U14-U16, §U15-U17 and §U18-U19 must-reuse lists: is every item used, or is the review's
  reason for not using it right (U14-U16: `length_runWith`, `DAGGate.getD_lt_depth`, `encrypts_encrypt`, `evalKey_eq`,
  `levelKey_eq`, `levelGate_of_le`; U15-U17: `acceptProb_snd`, `exists_hybrid_gap`, `distAdv_comp`,
  `acceptProb_coins_fst`, `OneWay.uprob_update`, `fheView_eq`, `Seeds_eq`, `exists_fixSeed`, and the inapplicable
  `real_uniformKey_advantage`, `distAdv_multi_le_sum`, `distAdv_tuple_le_sum`; U18-U19: `PolyExpr.eval_var`,
  `LWE.Family.advantageAt_eq`)?
- The private helpers: is any of `four_pow_clog_le`, the seven `LeveledSecurity` helpers or
  `two_mul_width_lt_of_ratio` a restatement of a public TCSlib, Batteries or Mathlib lemma, or a copy of another
  file's private lemma (e.g. `Hybrid.lean`'s private `acceptProb_plant`, `Symmetric.lean`'s private
  `exists_equiv_symEncrypt`)? Is either public helper a restatement (e.g. against phase 5's `homGate_encrypts`,
  `LWE.Family.encodeChallenge_length_le`)?
- The inline facts the reviews probed (each, per G53-01, with the use's hypotheses: check the probe sources in the
  evidence): U14-U16 **D1–D7** (`2^⌈log₂ y⌉ ≤ 2y`, `four_pow_clog_le`, the general `b^clog b y ≤ b·y`,
  `(!b).toNat = 1 − b.toNat`, the `LWE.sample` identity, `decrypt P s (gadget P) = true`, `β ≤ bootNoise P β`);
  U15-U17 **D1, D2, D4** (no lemma) and **K1, D3, D5** (timeouts at 400k and 3.2M heartbeats, decided by name and shape
  searches: is that decision right?); U18-U19 **E1–E6** at B6 (E1 the helper's statement; E2 `Nat.clog 2 n ≤ n`; E3
  `β ≤ bootNoise P β`; E4 the glue's arithmetic core; E5, E6 nonnegativity), with the controls K2, K3. Is any of them,
  or any other inline step, a public TCSlib, Batteries or Mathlib lemma at the pinned revisions (search by name and by
  statement shape)?
- The near relatives the reviews record (U1416-F04, U1517-F04, U1819-F03): shared proof text with phase 5
  (`eval_encrypts`, `homGate_encrypts`'s `¬` step, `distAdv_encrypt_le`'s inline two-bit step, its `have hN`). None is
  a stated lemma; is that right?
- Is DL-71's description complete and accurate for the three accepted facts, and did anything escape it? Anything the
  issued sweep and the reviews missed?

**F. Policy and form** (`policy.md` §1–§3, COMMON §5.4–5.5). Every proof of about 20 lines or more has a sketch, with
step comments at its major `have`s (the reviews list: `encrypts_bootGate` 31, G10 35, G12 26, G13 24, L2 60, L3 34; the
`LeveledSecurity` helpers 87, 41, 34 and L4, L5 32 each; G16 23, A1 35, A3 85); every helper has a formula docstring and
"Glue." (after LE-u1517-doc for `LeveledSecurity`); no new or changed source tag or anchor (the targets' citations are
B6's; the helpers carry "Glue." and no tag); width ≤ 100, no micro sign; sizes (§7): Bootstrap 518, Leveled 384,
Circular 161, LeveledSecurity **697** (over the 600 target, under the 1,000 cap; U1517-F05; LE-u1517-doc adds 16
lines), PolyRatio 245, Asymptotic 458.

**G. Rule 10.** Does any proof read a foreign TCSlib definition other than through a published reader? Read every name
passed to `rw`/`simp`/`simpa`/`simp only`/`unfold`, and every `rfl`/`decide`/`show` step (G15's pointwise `rfl`;
`hsec`'s `rfl` in the uniform-key helper; the own readers' `unfold bootGate`/`levelGate`, which are frozen and own).
Then grade the maintainer's seal evidence:
- the reviews' phase 2 (§ P2-5 of each `phase2.md`): canonical coe-A and seal B over the whole closure, 0 errors
  (Bootstrap 444, Leveled 479, Circular 464, LeveledSecurity 1,561/1,562, PolyRatio 1,394/1,395, Asymptotic
  1,653/1,654); liveness pairs ALL_OK (6 for U14-U16, two of them for `encrypts_bootGate`; 4 for U15-U17; 4 for U18-U19,
  one for the helper); the explicit-unfold scans (0 foreign definitions); U18-U19's own-definition seal of
  `PolyRatio.lean` (`ofFamily`, `pBoot` irreducible from the helper on, with its NEG control);
- the landing re-check at the head: canonical coe-A on all six owners, rc 0, 0 errors, requested = verified (Asymptotic
  **1,654**: one more than the review's B6 count because `LeveledSecurity`'s private `levelPosHybrid` is now in its
  closure); the paired controls for the two helpers (`bootGate` pair and sealed use of `encrypts_bootGate` in
  `Leveled`'s sealed copy; the `ofFamily` pair of `ofFamily_columns_le` in `Asymptotic`'s), ALL_OK.
- Is that sufficient, and is anything sealed or excluded that should not be (the excluded abbreviations are listed in
  each seal record)?

**H. The evidence binding** (§ *Evidence binding*). Does each piece bind to the PR's code? Is anything necessary
missing or unverifiable? The reviews' replays ran on scratch heads on no ref (each unit on B6; stacked on the records
tip; the full stack `6e363a29`); the landing re-check ran on the PR head itself. A missing or non-binding piece of
necessary evidence is a **major**.

**I. Is anything undisclosed?** Among the commits, the PR description, the three reviews and phase-2 reports, the
workers' `REPORT.md`s, the landing re-check and the records, is any change, claim or omission undisclosed? The known
slips are below. Grade the review findings **U1416-F01..F05**, **U1517-F01..F05** and **U1819-F01..F03** in a separate
table (agree, or regrade with the reason).

## Evidence binding

| Evidence | Bound to | What it shows | Reaches the PR head by |
|---|---|---|---|
| Deliveries `inbox/fills/gsw-6b-u14-u16/`, `-u15-u17/`, `-u18-u19/` (exchange finals `90b4c3a1`, `f501b669`, `c414248e`) | worker heads `9852429ef14ce063fcf11ff860e7262f92063d55`, `619d202992b026ab7464595884d9b1b77736d8ab`, `4672ed30d036feb624ca84b4199af19d77f5768f` on B6 | the patches, `src/`, the workers' evidence (seals, axioms, controls, census) and `REPORT.md` | patch-id 7/7 equal; fills-head blobs = delivered `src/` |
| U14-U16 `review.md`, `phase2.md`; `gsw-6b-u14-u16-final-r1-evidence.zip` (`36a92cb89c5e85a809f60dec4517f826cb57597e700b60f5eb4318f611420113`) | `9852429e` reproduced on B6; stacked head `cf4e56df65741a5b8a468aa57cc28d774d71185a` (records tip `c63ee44f` + unit, `TCSlib` `8dc09446`; on no ref) | integrity, reproduction, scope, decls2 1/0/0, helper statement, headers, frozen normalization with 13 controls; B6 10/10 and stacked 12/12 rc 0; axioms 65 constants; coe-A/seal B 444/479; 6 liveness pairs; unfold scan; D1–D7; lint | `frozen/{Bootstrap,Leveled}.head.lean` = the PR head's blobs; `.base.lean` = B6's (§5) |
| U15-U17 and U18-U19 `review.md`, `phase2.md`; `gsw-6b-u15-u17-u18-u19-final-r1-evidence.zip` (`ff76e89961ce42254530e3ac9e700925a1cdaf870ec31d9808fe453cd783865d`, filed in both folders) | `619d2029`, `4672ed30` reproduced on B6; stacked heads `67a69bae2b352fcc584c9cad1f34b3d51fde9d21`, `0656a95a024c10107a067b680fc6b50c7ef4bdf4`; **full 6b stack `6e363a298ff6fe59e861f968d4c54262d96e9f74`** (`TCSlib` `37ae0f32`; on no ref) | the same checks per unit (decls2 0/0/0 and 1/0/0; frozen normalization with 11 and 6 controls; `heff` kept); B6 7/7 and 6/6, stacked 12/12; the full stack 12/12, 0 `sorry`, admissions 18 in 8, 103 constants 0 `sorryAx`; coe-A/seal B; 2+2 and 4 liveness pairs; own-definition seal; unfold scans; probes; lint; `proposed/LE-u1517-doc.diff` | `frozen/*.head.lean` = the fills head's blobs (four files); the fills head's `TCSlib` tree = `6e363a29`'s; the PR head's `LeveledSecurity.lean` = `proposed/LeveledSecurity.LE-u1517-doc.lean` |
| **Landing re-check** `landing-u14-u19-recheck-evidence.zip` (this directory; SHA-256 in `staging-checks-r1.txt` §8) | the PR head `dd6d274e` itself, on a copy of snapshot #11 | 12/12 rc 0 incl. root, 0 errors, 0 warnings, state check 1,456 OK; admissions 18 in 8; axioms of the 15 targets and both helpers (168 constants, 0 `sorryAx`); coe-A on the six owners 0 errors; the helpers' paired controls ALL_OK; decls2 2/0/0 vs the records tip; lint; the docs-only check; the application logs | `run/land/` binds every rebuilt module's source SHA-256 to `git show dd6d274e:<path>` (stateplan update); the seal records carry the source SHA-256 at `dd6d274e` |
| This pack's `staging-checks-r1.txt`, `source-head-r1.json`, the diffs | the PR head and the records tip at staging | pins, Lean equality, scope, patch-ids, blobs, removed-line classes, headers, file statistics, the ZIPs' manifests, the records' SHA-256 | git objects only |

The evidence ZIPs' inner `SHA256SUMS` verify (264/264, 475/475, 155/155; none lists itself; §8). The scratch heads
cannot be fetched (they are on no ref); their binding is through the `TCSlib` trees and the blobs, which the auditor can
check from the PR branch and the ZIPs. The landing re-check did **not** re-run seal B, the units' other liveness pairs,
the unfold scans or the duplication probes: the code of the six files at the PR head is that of the fills head (comments
aside), whose runs the reviews hold.

## Known dispositions and slips (not findings)

- **Review findings:** U1416-F01 (minor, records side: the sweep missed `m·B ≤ bootNoise P (m·B)`; ruled, DL-71),
  U1416-F02 (info: G12's `hs`, the third inline copy of the `LWE.sample` identity; DL-71), U1416-F03 (info: the private
  `four_pow_clog_le` is new content), U1416-F04 (info: proof text shared with phase 5, within the allowance), U1416-F05
  (info: report count slips, seal-count method, host housekeeping); U1517-F01 (info: the pack's L4 hint could not
  reach `levelTerm`; worker's route ruled acceptable, Q-U1517-1 A), U1517-F02 (minor: helper form; **fixed by
  LE-u1517-doc**), U1517-F03 (info: `0 ≤ 2·(N·ε)` at a constant test), U1517-F04 (info: an undisclosed near relative,
  phase 5's inline two-bit step; recorded by the review), U1517-F05 (info: `LeveledSecurity.lean` over 600 lines);
  U1819-F01 (info: = U1416-F01 from the other side; DL-71), U1819-F02 (info: A1/A3 sketches; **fixed by
  LE-u1819-doc**), U1819-F03 (info: small inline repetitions; `distAdv` nonnegativity in DL-71). **Grade them.**
- **Order of application.** The branch applies U14+U16, then U15+U17, then U18+U19 (the order of the 6b fill
  rulings). `ISSUED/README.md` §Landing order lists U15-U17 before U14-U16 for separate PRs; the six files are disjoint,
  each worker commit still equals its delivered patch, and the resulting `TCSlib` tree is the reviewed full stack's.
- **Commit metadata.** `git am --committer-date-is-author-date` kept the workers' author and committer data, so the
  committer dates are not monotonic along the branch (U18+U19's commits, 00:46:41Z, follow U15+U17's L5, 01:07:12Z), and
  U18+U19's two commits carry the same timestamp, as delivered (`COMMITS.tsv`). All nine commits carry SSH signatures of
  the account's shared Claude key (BS-F08); none was cryptographically verified (no allowed-signers file). The workers'
  commits are unsigned.
- **LE-u1819-doc's scope.** It names `Parameters.ofFamily_columns_le` in A1's and A3's sketches and drops A1's claim that
  `hm` is read through `Parameters.ofFamily_width` (the proof uses `ofFamily_lwe` only). It does not add the other
  omissions U1819-F02 lists for A3's sketch (`Negligible.const_mul`, the `Finset` counting lemmas): the ruling asked for
  the helper's name only.
- **Seal counts.** The reviews' seal request counts are on B6 + unit; the landing re-check's are on the PR head. They
  agree except Asymptotic (1,653 → 1,654, `levelPosHybrid`).
- **PR description.** At staging the PR is not open. `pr-description.md` is the body the PR is to be opened with; if the
  opened body differs, the maintainer re-takes this file before dispatch. "6 files, +883 / −90; 9 commits" are the
  branch's numbers; the seal numbers in it are the landing re-check's.
- **Hashes in the reviews:** each review reproduced its unit's worker commits **unsigned on B6**; the PR's commits are
  the same patches signed on `53e430b6`, so their hashes differ (`source-head-r1.json` `commits`). The reviews' records
  tips (`c63ee44f`, `c87eb403`, `a25338e0`) have `TCSlib` tree `745bf4b4`, the same as `53e430b6`.
- **No Lean, no `lake`** was run for this staging. `staging-checks-r1.txt` is git objects and `python3 -I` only; the
  landing re-check is the one in-house Lean run after landing.

## Merge interaction (maintainer merge conditions, not audit items)

- PR × the records tip at staging: the PR head descends from it; the merge's `TCSlib` tree is `004dfaef` (the head's).
- **Adoption:** snapshot #12 from a fresh replay of whatever merges (about 12 modules; the re-check tree was deleted).
- No other open PR touches the six files (the 12 open PRs' file lists, read at staging).
- EF-R1 (Q-6BF-4 A) lands stacked later and may use `Parameters.ofFamily_columns_le`; the DL-71 cleanup follows the
  merge.

## Files of this directory

- **`pack-r1.md`** (this file) and **`dispatch-r1.md`** (the Codex prompt; postdates the pin; not in `SHA256SUMS-r1`).
- **`pr.diff.txt`**: `git diff origin/cryptography/pass-shelat-ch2-4...dd6d274eba9b55b5a2c7c97730245a4f1bea1e90`
  (= `git diff bff0567b dd6d274e` over the six files, byte for byte).
- **`pr-u14-u16.diff.txt`** (`53e430b6..96e22a6d`), **`pr-u15-u17.diff.txt`** (`96e22a6d..1664c477`),
  **`pr-u18-u19.diff.txt`** (`1664c477..103a8bde`) and **`pr-landing-edits.diff.txt`** (`103a8bde..dd6d274e`).
- **`pr-description.md`**: the PR body the PR is to be opened with (see the slips).
- **`landing-u14-u19-recheck-evidence.zip`**: the landing re-check (`land-u1419/PROVENANCE.txt` first; inner
  `SHA256SUMS`, 155 rows, not listing itself).
- **`source-head-r1.json`**: pins, Lean equality, the nine commits (parents, trees, author, committer, signature kind,
  files, patch-ids against the delivered patches), the deliveries, the six files' blobs and statistics at B6, the fills
  head and the PR head, the review files' and ZIPs' SHA-256, and the SHA-256 of every record this pack cites at the
  records tip.
- **`staging-checks-r1.txt`**: the staging's checks, §1–§10.
- **`SHA256SUMS-r1`**: the files above other than `dispatch-r1.md`.

## Findings delivery

Return **`findings-r1.md`** as Markdown in the Codex chat. If you have evidence files (search logs, scripts), return a
ZIP with `findings-r1.md` at its root. Push nothing, write nothing to the repository, open no PR. The user dispatches
and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Number the findings **G55-01, G55-02, …**. Grade U1416-F01..F05, U1517-F01..F05 and U1819-F01..F03 in a separate table.
Report the audited head, the records pin, the four evidence ZIPs' SHA-256 as you computed them, the searches you ran
(with hit counts and, for every `exact?`-style or shape search, the hypotheses it carried), the counts by severity, and a
verdict for **PR #396**:
- **CLEAR:** zero blockers and zero majors.
- **HOLD:** otherwise.

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish its frozen statement, or a scope
  violation (a change outside the six owned files, outside COMMON §4's permitted regions, or a public declaration other
  than the two Q-6BF-3 helpers).
- **major:** any of the following:
  - a changed frozen header, statement prose, definition, reader, instance or `set_option`;
  - a forbidden read (Rule 10) not covered by the rulings;
  - an undisclosed copied private lemma, or an undisclosed (or unaccepted) re-proof of a public one, including an
    inline re-derivation of a TCSlib, Batteries or Mathlib lemma (DL-71's three facts are accepted);
  - a landing edit that changes code;
  - a fabricated source tag;
  - necessary evidence that cannot be verified or does not bind to the PR head.
- **minor:** documentation or API defects, including an inaccurate formula docstring, glue note, proof sketch, module
  sentence, review statement or PR description.
- **note:** anything else.
