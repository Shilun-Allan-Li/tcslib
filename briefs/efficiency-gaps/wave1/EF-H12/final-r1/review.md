# EF-H12 `ef-h12-levin-3col` · final r1 · maintainer review (phase 1 static, phase 2 Lean replay)

**Verdict after phase 2: ACCEPT WITH LANDING EDITS, conditional on EF-H12-R1 (A).** Phase 2 passed,
with one new minor finding: EFH12-F08, a landing edit. The details are in
[`phase2.md`](phase2.md).

**Phase 2 (2026-11-18, 12:23–13:36 UTC)**
- **Check head.** The 19 patches on `bff0567b` give `63d619e8`, whose tree `efdd41d8…` is the
  predicted one.
- **Build.** The predicted 16 modules, including the root `TCSlib` and `audits/pass-shelat/Checks`:
  rc 0, with 0 errors, 0 `sorry` and 0 warnings.
- **Axioms.** All 483 stored constants are standard, and the 245 decls2 constants equal the
  worker's axiom sets.
- **Seals.**
  - Strict: 11/11 with 0 errors.
  - Canonical coe-A and seal B: 10/11 with 0 errors. In both, `Verifier` fails only at
    `polyTimeComputable_stripCert`, a foreign-matcher read (F08).
  - `Bridge.lean`: the minimal unseal passes. Each of 20 readers needs exactly its named definition.
    The 7 `simp [EdgeRelation]` readers need none, because they read through equation lemmas.
  - Controls: 50 pairs, ALL_OK.
  - Explicit-unfold scan: 7 hits, all in `Bridge.lean`.
- **Bridge demonstrations.** Necessity: all 46 reader uses fail without the readers. Owner form: the
  27 readers compile in their 5 owners.
- **Landing-edit probes.** LE-h12-pow compiles, and its 10-module downstream is rc 0. `ProbeH12`
  passes at the check head.
- **Lint and snapshot.** Lint is unchanged, and snapshot #11 rehashes 0/0/0.
- **Findings.** **F03 and F04 are closed. F05 is partly closed:** (a) and (b) are closed; (c) is a
  landing edit and (d) stays on record.

The headline is real. `TCSlib.Cryptography.levinNPHard_L3COL : LevinNPHard L3COL R3COL` takes no
hypothesis. The statement of `LevinNPHard` and `LevinReduction` is used exactly as in
`ZeroKnowledge/NP.lean:134`/`:654`. The two one-line ZK corollaries restate the conclusions of
`zk_proof_of_witnessRelation_of_owp` and `zk_proof_of_mem_NP_of_owp` verbatim, without the
`LevinNPHard` hypothesis. The worker's evidence reports standard axioms and no `sorryAx` for all
three. Every instance and witness map is a `PolyTimeComputable` string map, and no efficiency claim
enters as a hypothesis.

**What holds the verdict back:**
- **EFH12-F01 (major, pending Seyoon).** The proof reads 27 foreign definitions through the
  quarantined `LevinHardness/Bridge.lean`. This rests on a "Readers in our files" ruling that is
  **not confirmed by Seyoon** and is not in the records. The bridge is also wider than the ruling
  as checkpoint 1 reported it.
- **EFH12-F02 (major, small landing edit).** `UnaryArith.unaryPow_poly` is an undisclosed
  re-derivation of a special case of the public `EncodingMachines.unaryPolyOf_poly`.
  `unaryDiv_poly`/`unaryMod_poly` are new-name restatements of `divNum_poly`/`modNum_poly`,
  disclosed only in the module docstring.

**Other findings:**
- minors EFH12-F03 to F07: evidence gaps, stale text, disclosure gaps and attribution wording. After
  phase 2, F03 and F04 are closed and F05 is partly closed.
- **EFH12-F08 (minor, new in phase 2):** a foreign-matcher defeq read in
  `polyTimeComputable_stripCert`; a landing edit.
- information EFH12-I1 to I6.

**Phase 1 was static only:** no Lean was run, because the machine's three Lean slots belonged to
other jobs. Phase 2 (plan below) ran as a separate job on 2026-11-18. Its results are in
`phase2.md` and `ef-h12-final-r1-evidence.zip` (SHA-256 in `evidence-SHA256SUMS`).

## What was reviewed

- **Delivery.** `inbox/fills/ef-h12-levin-3col/` on `exchange/pass-shelat-ch5-8`, at commit
  `36d9ac03c329544d33b1f3f9a73e6ce32152dde2` ("fill ef-h12-levin-3col: final"). This was also
  the exchange tip at review time.
  - The commit's parent is `226ae633`. It is unsigned (0 `gpgsig`) and touches only the unit's
    folder.
  - **The tree.** I extracted it with `git archive` into a fresh scratch directory. It has 1,685
    files:
    - `REPORT.md`;
    - 19 patches with `COMMITS.tsv`;
    - `src/` (14 files);
    - `evidence/` (1,648 files).
  - **Manifests.** The top-level `SHA256SUMS` is `92e5405e…`; `evidence/SHA256SUMS` is `5f53bf27…`.
- **Contract.**
  - `briefs/efficiency-gaps/wave1/EF-H12/brief.md`, `COMMON.md`, `rulings.md` and `README.md` at
    the records pin `54dcb3021a389831e7f94c3f82616cb7594fa574`. Since the pin, the brief,
    `COMMON.md` and `rulings.md` are unchanged. The `README.md` and the dispatch prompt changed
    only in their pin and EF-D4 lines.
  - Handoff §2 rules 15 and 16.
- **Rulings in force.**
  - Q-H12-1 A: the circuit route.
  - Q-H12-2 A: ingest [AB09] ch. 2 and 6 and a 3-colouring source **before** the delivery review.
    This is **still pending**; see EF-H12-R4.
  - Q-H12-3 A: re-derive `sat3Coloring`, disclosed; the course file stays read-only.
- **Background.**
  - Decision-log rows 903 (checkpoint 1, exchange `0ccb8c0e`, worker head `d2272e8e`: the
    E-SCOPE and the reported ruling) and 910.
  - The method precedent `EF-D1/final-r1/review.md`.
- **Base.** REC `cf6a2266e9556ca8ad61e56f7232266ccc6d4e62`, tree `d52cf05b…`, verified with
  `git rev-parse`.
- **Tools.** `python3 -I` and `git` only.
  - Scratch work is under
    `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/efh12/`:
    the delivery, a sparse alternates-backed replay repository, and my scan and recount scripts.
  - Nothing was pushed, and the main checkout was only read.

## Checks

| Check | Result |
|---|---|
| **Integrity** | **PASS, with one gap (F05d).**<br>• Both manifests pass `sha256sum -c`.<br>• There are no duplicate paths and no leading `./`, and neither manifest lists itself.<br>• `evidence/SHA256SUMS` equals the evidence tree exactly.<br>• **Gap:** the top-level `SHA256SUMS` (1,683 rows) omits `evidence/SHA256SUMS`, so that manifest is not bound by the top level. EF-D1's top level listed it. |
| **Reproduction (C13)** | **PASS: 19/19 hashes reproduced.**<br>• Method: `git am` at `cf6a2266` in a sparse scratch repository, with signing off and committer name, e-mail and date per `COMMITS.tsv` row. The author data matches too.<br>• The head is `c8d5b3c7f8733f3ea87fc701fbc83abc53bdb338`, which equals REPORT's head.<br>• No commit has a `gpgsig`.<br>• `src/` equals the head byte for byte, 14 of 14 files, and the path sets are equal.<br>• **Against checkpoint 1:** commits 1–8 are checkpoint 1's own (`d2272e8e` is commit 8); commits 9–19 are new. |
| **Scope** | **PASS.**<br>• `git diff --stat cf6a2266 c8d5b3c7` gives 14 paths, +4,000/−0:<br>&nbsp;&nbsp;– 13 new files under `ZeroKnowledge/LevinHardness/` and its facade;<br>&nbsp;&nbsp;– `ZeroKnowledge.lean` +3, which is one `import` plus a two-line `## Contents` entry.<br>• **No `TCSlib/Complexity/**` file and no existing ZeroKnowledge file is touched.**<br>• The brief allows the split into 12 files (each under 1,000 lines), and REPORT lists them. |
| **Disjointness** | **PASS.**<br>• All 14 paths are new or the facade.<br>• None is a Stage 2 owner path. The bridge's *proposed* owner reader `levinNPHard_iff` would land in `ZeroKnowledge/NP.lean`, which **is** a Stage 2 owner file (`scope.tsv` S2-SL-481..487, S2-BO-190/191). That is relevant to R1, not to this PR.<br>• None of the 25 local Arora–Barak/Ladner branches (`arora-barak*`, `codex/ab34-*`) changes the four Complexity owner files of the bridge. |
| **decls2 (C3)** | **PASS.**<br>• Pinned `decls2.py` (`fa81981a…`, equal to the delivered copy), run by me on the reproduced head against the base.<br>• **245 ADDED, 0 CHANGED, 0 REMOVED.**<br>• My output is byte-identical to `checks/c3-decls2.txt`. |
| **Statements of the headline** | **PASS.** Read from the source (Hardness.lean):<br>• `levinNPHard_L3COL : LevinNPHard L3COL R3COL` has no hypotheses. The proof enters `LevinNPHard` only through `Bridge.levinNPHard_iff` (F01).<br>• The `LevinReduction` built has `f x = padWord (colorInst (dagCktSatToSAT3 (f₁ x))) B(|x|)`, `w x y = padColWord (colorWord … (wireValues (f₁ x) (certOf q x y))) B(|x|)` and `p = B·B`.<br>• All six fields are proved: `f_poly`, `w_poly` on `⟨x, y⟩`, `mem_iff`, `witness`, `length_eq` for **every** `x` (`length_padWord`) and `le_eval`.<br>• The corollaries' conclusions are textually those of `NP.lean:689` and `:742`. |
| **Rule 15** | **PASS.**<br>• Every instance and witness map is an explicit string map with a `PolyTimeComputable` theorem: `polyTimeComputable_tabInst`, `polyTimeComputable_certOf`, `polyTimeComputable_wireValues`, `polyTimeComputable_colorInst`, `polyTimeComputable_colorWord`, `polyTimeComputable_padWord`, `polyTimeComputable_padColWord`, and `polyTimeComputable_dagCktSatToSAT3` reused.<br>• Each is unconditional, except the combinator rows (`…_verTest (hb)`, `…_hasRec (hS hR)`, the unary rows), whose hypotheses are the poly-time of their arguments, and `polyTimeComputable_colorInst_of` (I2).<br>• No `NUPPT`, no `∃ A : NUPPT, A.Computes`, and no `heff`-style hypothesis.<br>• `M` comes from `polyTimeComputable_iff` inside the proof, and its efficiency is part of the same existential, so this is not a `Classical.choice` machine without proof.<br>• The search hosts are registered: `EncodingMachines.polyTimeComputable_firstIdx` for the boundary search, `polyTimeComputable_transduce` for the automata, and `ComposeMachines.polyTimeComputable_flatMap_range` for tabulation. The wire values re-run the registered `CircuitEval.evalTM` per wire on a re-targeted description, so there is no new evaluator. |
| **Admissions (C4)** | **PASS.**<br>• 0 `sorry`, `admit`, `native_decide`, `axiom` and `opaque`.<br>• 0 `@[simp]`, 0 `attribute` lines.<br>• No existing file's code changed. |
| **Hygiene** | **PASS.**<br>• Sizes: 53 to 720 lines per file, at most 100 characters wide.<br>• Copyright headers, `relaxedAutoImplicit false`, `autoImplicit false`, and `maxHeartbeats 0` (house form).<br>• Every public declaration has a docstring.<br>• Every theorem proof of 20 lines or more has a `**Proof sketch.**` (my parser found 0 missing).<br>• Every definition has an `_eq`/`_iff`/`_apply` reader.<br>• Total 4,000 lines against the brief's 2,000–3,800 ±40% (at most 5,320). |
| **Lint (C8), recomputed** | **PASS.**<br>• `style_lint.py` on the 14 files: 0 findings.<br>• `campaign_style_lint.py TCSlib/Cryptography --check8b`: base 92 FAIL / 103 WARN over 531 files; head 92/103 over 544.<br>• The FAIL/WARN line sets are identical, and equal to the worker's `c8-campaign-head.txt`. |
| **Frozen files (C7)** | **PASS.** The worker's `c7_frozen.py` reports 3 allowed insertions and 0 other differences, and its one-character control fails as required. My diff agrees. |
| **Clashes (C10)** | **PASS.**<br>• I grepped 13 distinctive new names (`levinNPHard_L3COL`, `LevinHardness`, `wireValues`, `colorInst`, `gadgetColor`, `padColWord`, `R_3SAT`, `R_CKT`, `certOf`, `verTest`, `gadgetN`, `unaryDiv_poly`, `polyTimeComputable_foldl_accept`) over the `TCSlib/` and `audits/` Lean files of all **336 distinct local heads**: 0 hits outside the delivery.<br>• Positive control: `encGraph_mem_L3COL_iff` is hit on 155 heads.<br>• The worker's two shared short names (`decode_eq`, `padGraph`) are in other namespaces.<br>• The worker's C10 counted 244 constants, which predates `verTime_eq` (F05b). |
| **Axioms (C5), recounted from `axioms/stmtdump.txt`** | 245 constants, the same set as decls2:<br>• 116 with all three of `propext`, `Classical.choice`, `Quot.sound` (in various orders);<br>• 44 `[propext]`;<br>• 38 `[propext, Quot.sound]`;<br>• 47 `[]`;<br>• **0 `sorryAx`**, 245 STD.<br>• The headline and both corollaries are `[propext, Quot.sound, Classical.choice]`.<br>Phase 2 recomputes these independently. |
| **Build (C1), recounted** | 14 modules: rc 0, 0/0 errors, 0 `sorry`. The 14 logs are empty (`e3b0c442…`), and each source SHA-256 in `summary.txt` equals `git show c8d5b3c7:<path>`, which I re-hashed. |
| **Downstream (C2)** | **Incomplete in phase 1 (F04); closed by phase 2.**<br>• The root `TCSlib` was not built (PFR oleans).<br>• `audits/pass-shelat/Checks.lean` imports the changed `ZeroKnowledge` facade but is not listed: REPORT says the root is the only importer.<br>• **Phase 2:** both are rc 0 on snapshot #11, 16/16 modules. |
| **Seals (C6), recounted** | **Partial (F03).**<br>• *Plain:* 11 non-bridge owners, each sealed copy minus its single `attribute [local irreducible]` line equals the head source; Gadget has 0 candidates and an added comment line only. Each seal line's names equal the delivered candidate list (30/15/26/13/0/48/9/5/17/5/16). Every results line reads PASS (rc 0, 0 error lines).<br>• *Bridge:* the sealed copy minus seal and unseal wrappers equals the head. Its 20 names equal the candidates, and the run is PASS with 27 named exclusions.<br>• **Only the strict whole-file seal was run.** Canonical coe-A and seal B were not run, and raw Lean logs are not kept.<br>• 9 bridge declarations unseal more than the definition they are named for (F03).<br>• *Controls:* 9 pairs, one per owner with definitions. Each NEG fails exactly once (line 5), each POS passes, and unsealed runs have 0 errors.<br>• *Explicit-unfold scan:* my own TCSlib-name scan of the 11 non-bridge files reproduces the worker's adjudication. The only hits are lemma *arguments* (`DAGGate.encode/decode`, `CNF.serialize`) and own-file `unfold gadgetAdj`, so **0 foreign unfolds outside Bridge.lean**. |

## The headline, statement by statement

- **Target map.** Every brief target maps to a declaration (REPORT *Target map*), and I checked the
  map against the source.
- **`exists_levinReduction_L3COL` is not stated.** The brief allows keeping one of the two.
- **`decodeCert` is not defined.** It would only wrap `Turing.splitAtLastTrue`;
  `splitAtLastTrue_certOf` is its reader.
- **The polynomials, as REPORT gives them:**
  - `m(n) = q(n) + 1`;
  - `T(n) = C (2n + 3 + m(n))^c + 1` (`eval_verTime`);
  - `N(s) = 3 + 2|s| + 6 (2|s|)³` (or 4 for `K₄`);
  - `B(n) = A (n + 1)^a + n + 1`, from `output_length_le` of the unpadded composite;
  - `p = B²`.

  They are explicit up to the decider constants of the given witness relation, as in
  `dagCktSatLang_NPHard`. `|f x| = O(|x|^{6·deg})`, which is polynomial.

## Statement changes (disclosed; all justified)

1. **`mem_SAT3_iff_exists_R_3SAT` is replaced by `exists_R_3SAT_iff`** (fan-in-two `C`):
   `(∃ a, R_3SAT (dagCktSatToSAT3 C.encode) a) ↔ ∃ x, C.eval x = true`.
   - **Justified.** `Complexity.SAT3` (`ClassNP/SAT.lean:122`) has no published reader; I checked
     `git grep` at REC and found none.
   - The composite chain `x ∈ L ↔` tableau satisfiable `↔ ∃ a, R_3SAT … ↔ f x ∈ L3COL` never
     needs `SAT3`.
   - **No weakening:** `R_3SAT` is the brief's relation verbatim (`Relations.lean`).
2. **The verifier does not test `|u| = m(|x|)`.** The circuit has exactly `m(|x|)` inputs (its
   type), and the witness map `certOf` has exactly that length (`length_certOf`). Justified.
3. **The hard-wired prefix is `⟨x, []⟩`** (`pairEncode_nil_append`). This removes a length-split
   search. Justified; it is the brief's item (a) specialization.
4. **Isomorphism becomes a homomorphism `ReductionGraph (gadgetFormula K mem) →g gadgetSimpleGraph K mem`.**
   - Soundness needs only the pull-back of a colouring.
   - Soundness is still exactly one application of `SATtoColorReduction` (`Soundness.lean:216`):
     **no second soundness proof**.
   - Completeness is the explicit colouring, as the brief's step 4 requires anyway. Justified.
5. **One gadget per clause code `c < (2K)³`, with `K = |s|`**, instead of per de-duplicated
   clause.
   - This matches `OutputVertex (Fin K)`, which has a gadget for every clause.
   - Ill-formed or over-wide inputs go to `K₄`, and malformed strings decode to the empty
     formula, consistently with `R_3SAT`.
   - It costs a cubic vertex count, which is still polynomial. Justified, with disclosure.
6. **`exists_levinReduction_L3COL` is omitted** (above).
7. **`properColoring_padGraph` drops `n ≤ B`.** This is a strengthening.

**No silent weakening found.**

## `Bridge.lean`: the readers, one by one

The ruling as reported (checkpoint 1, REPORT) is "Readers in our files". **It is unconfirmed by
Seyoon**; the only record is the worker's report (decision-log row 903 says "to confirm with
Seyoon"). The ruling is asserted as fact in three library docstrings: `Bridge.lean:18`,
`Soundness.lean:23` and `LevinHardness.lean:35`.

I compared every reader with the owner's definition at REC.

| # | Reader | Owner (REC line) | Proof | Matches owner body |
|---|---|---|---|---|
| 1 | `levinNPHard_iff` | `ZeroKnowledge/NP.lean:654` (J6; Stage 2 owner) | `Iff.rfl` | yes, verbatim |
| 2 | `toCNF_eq` | `CircuitComplexity/DAGCircuitSat.lean:267` | `rfl` | yes |
| 3 | `widthAtMost_iff` | `Formulas/CNF.lean:102` | `Iff.rfl` | yes |
| 4 | `numVars_eq` | `Formulas/CNF.lean:96` | `rfl` | yes |
| 5–7 | `serializeLit_eq`, `serializeClause_eq`, `serialize_eq` | `Formulas/CNFEncoding.lean:99`, `:104`, `:110` | `rfl` | yes |
| 8–9 | `decode_eq`, `fallback_eq` | `CNFEncoding.lean:175`, `:169` | `rfl` | yes |
| 10 | `syntaxStep_eq` | `CNFEncoding.lean:608` | **`fin_cases q <;> cases b <;> rfl`** | the owner's `match q.val` restated as an `if` chain: a case lemma, not the body |
| 11 | `syntaxOK_eq` | `CNFEncoding.lean:723` | `rfl` | yes |
| 12–13 | `satisfiesLiteral_pos`, `_neg` | `NPReductions/ThreeSATToColoring.lean` (course material) | `rfl` | the two match arms |
| 14–17 | `satisfiesClause_eq`, `satisfiesSat3_eq`, `isSatisfiable_iff`, `is3Colorable_iff` | same file | `rfl`/`Iff.rfl` | yes |
| 18 | `reductionGraph_adj` | same file | `Iff.rfl` | yes (the `Adj` field) |
| 19–27 | nine `edgeRelation_*` case lemmas | same file | **7 by `simp [EdgeRelation]`** (one `simp only`), 2 by `cases`/`fin_cases` + `rfl` | **derived characterizations**, not the body. Example: `edgeRelation_literal_literal` turns the two `x = y` arms into an existential; the `palette 0` arms become `i = 0`. |

**Consumers** (grep of `Bridge.<name>` over the 11 other files):
- `levinNPHard_iff` and `widthAtMost_iff` are used in Hardness;
- `toCNF_eq` in CircuitWitness;
- the 8 CNF and serialization readers in ColoringParse;
- the 16 course-file readers in Soundness.

All 27 are used.

**Nothing else reads foreign bodies (statically).**
- The strict seal of the 11 other files passes with every collected candidate sealed (recount
  above).
- My scan finds no foreign definition passed to `simp`/`rw`/`unfold`/`delta` outside the bridge.
- Definitions without readers that the job needed were routed around, not read:
  - `Complexity.SAT3` (statement change 1);
  - `DAGCircuit.Satisfiable` (through `toCNF_extension_iff`);
  - `CktSatReduction.descTail` (the job's own `descPrefix` transducer);
  - `Graph.ofSimpleGraph` (the restated `threeColorable_gadgetGraph_iff`, disclosed).
- Phase 2 confirms this with the canonical coe-A seal.

## Duplication sweep (binding)

**The brief's three disclosed overlaps are present and accurate:**
- **(a)** `Verifier.lean` re-instantiates the core of `dagCktSatLang_NPHard`
  (`CircuitSatNPHard.lean:93-127`) for an explicit verifier. It is a specialization with the
  `⟨x, []⟩` prefix and an explicit `PolyExpr` time bound.
- **(b)** `ColoringWitness.gadgetNodeColor`/`gadgetColor` re-derive the private
  `clauseGadgetColor`/`sat3Coloring` (`ThreeSATToColoring.lean:163-193`).
  - I compared the six-node table arm by arm: it is identical.
  - Properness is re-proved per edge family on the `Fin N` layout.
  - This is Q-H12-3 A.
- **(c)** `R_3SAT` states publicly the `u.getD v false` convention of `ClassNP/SAT.lean`'s private
  `satAssignment`.

**The checkpoint-1 promise (private unary helpers): kept.**
- The 27 `private` declarations of the job are all file-local. No name or statement is repeated
  across files.
- C's and B's private div/mod/`clauseLit`/`litVal` copies are gone. `ColoringGraph` and
  `ColoringWitness` now import the public `UnaryArith.lean`.

**The new public `UnaryArith.lean`, against the three places the prompt names:**
- **`FormulaKit/Emit.lean` (Complexity).** `unaryDiv_poly`, `unaryMod_poly` and `unaryPow_poly`
  are statement-identical to `polyTimeComputable_unary_div` (`:262`, `sorry`),
  `polyTimeComputable_unary_mod` (`:274`, `sorry`) and `polyTimeComputable_unary_pow` (`:237`,
  proved from the sorried `_mul`).
  - They cannot be cited without `sorryAx`.
  - This is disclosed (REPORT; worker question W2).
- **EncodingMachines unary rows (ZeroKnowledge, J6).** **EFH12-F02.**
  - `unaryDiv_poly`/`unaryMod_poly` are `divNum_poly`/`modNum_poly` (`EncodingMachines.lean:657`,
    `:678`) with the readers `divNum_eq`/`modNum_eq` folded in: one-line restatements under new
    names. The UnaryArith docstring says so; REPORT § *Overlap* does not.
  - `unaryPow_poly` re-derives by induction on `unaryMul_poly` the instance `p = var^n` of the
    public `unaryPolyOf_poly` (`EncodingMachines.lean:127`, with `PolyExpr.eval_pow`).
    **Undisclosed anywhere.**
  - `unaryDivConst_poly`/`unaryModConst_poly` are the constant-divisor forms. Their relatives are
    Cook–Levin's **private** `clA5Div_native`/`clA5Mod_native` (`CookLevin/Hardness.lean:7808`,
    `:7838`); not disclosed (F06).
- **`ClassP/BinaryArith`.** No unary div/mod/pow row exists there; it is binary arithmetic. No
  overlap.

**My sweep of every other new helper:**
- **Searched:** TCSlib at REC by name and by conclusion shape, the core `Std.Sat.CNF` sources of
  the v4.25.0 toolchain, and the 336 local heads for the names.
- **`clause_eval_eq_true_iff`, `cnf_eval_eq_true_iff`.** Core has only `eval_nil`/`eval_cons`/
  `eval_append`. No ∀/∃ characterization exists in core or TCSlib, so these are new.
- **`serialize_injective`.** It is derived from the public `CNF.parse_serialize`, not re-proved.
- **`polyTimeComputable_foldl_accept`.** This is the public form of `ClassNP/SAT.lean`'s
  **private** `satScanTM`/`satScan_computes` (`:231`–`:295`), derived from the public transducer
  row.
  - REPORT relates it to `satSyntax_poly` only.
  - `polyTimeComputable_syntaxOK` is **statement-identical** to the private `satSyntax_poly`
    (`SAT.lean:306`); not disclosed as such (F06).
- **`le_foldr_max_zero`** (private) copies the private `le_foldr_max_of_mem`
  (`Formulas/CNF.lean:112`). Disclosed.
- **`threeColorable_gadgetGraph_iff`** re-proves the 6-line pattern of
  `threeColorable_ofSimpleGraph_iff` (`ThreeColoring/Language.lean:116`), because
  `Graph.ofSimpleGraph` has no reader. Disclosed.
- **`padColWord`** is near `EncodingMachines.padTo` (`:824`; also
  `ThreeColoring/Machines.lean:303` and `ComposeSecurity/Machines.lean:223`); they agree for
  `|w| ≤ 2B`. Disclosed in the docstring.
- **`padGraph`**: unrelated to `Randomized.padGraph`.
- **`colorBits`** (private) is a per-vertex view of `encColoring`, proved equal through the
  published `getD_encColoring_two_mul*`. No public flatMap or poly-time row of `encColoring`
  exists to cite.
- **`stripCert`** names the inline function of the catalog row `computesFunInTime_stripLast`
  (`Primitives.lean:3259`). No named public definition exists.
- **`descPrefix`, `retarget`, `withOutput`, `wireValue(s)`.** No near-relative (0 hits; `CVAL` and
  `CVALPrefix` are output-only, as the brief said).
- **Gadget layout, codes, `memS`/`goodS`/`hasRec`, `widthStep`, padding.** New.

**The brief's must-reuse items not used,** each with a reason I accept:
- `LevinReduction.trans`/`.refl`/`.polyTimeReducible`: the composite is built directly, so the
  padding applies once.
- `mem_dagCktSatLang_iff_mem_SAT3`, `encode_mem_dagCktSatLang_iff`, `mem_dagCktSat_iff`: there is
  no `SAT3` reader, and the chain is by `eval`.
- `mem_P_iff`, `test_of_mem_P`: `mem_P_of_test` is used.
- `polyTimeComputable_polyUnary`: `polyTimeComputable_unaryPoly` is used.
- `forLoop`/`getW`/`chunkW`, `polyTimeComputable_iterate`: other registered hosts are used.
- `threeColorable_ofSimpleGraph_iff`: see above.
- `exists_witnessRelation_of_mem_NP`: used inside `zk_proof_of_mem_NP_of_owp`.

## Findings

**Blockers: none.**

- **EFH12-F01 (major, pending Seyoon: EF-H12-R1/R2). Rule 10: the bridge rests on an unconfirmed
  ruling and is wider than reported.**
  - **What it is.** `Bridge.lean` states 27 public readers of foreign definitions in a non-owner
    file. COMMON §4.3 says "A missing reader is a scope request, never an unfold". Without
    Seyoon's confirmation this is the EF-H11-F01 class of finding. With it, it becomes a recorded
    exception.
  - **Wider than checkpoint 1 reported:**
    1. **`levinNPHard_iff` reads `ZeroKnowledge/NP.lean`.** That is a J6 crypto file, not a
       Complexity file. It was added after the checkpoint (commit 12, `0c95b0b9`). `NP.lean` is a
       Stage 2 owner file (S2-SL-481..487, S2-BO-190/191).
    2. **Not all readers are `rfl`/`Iff.rfl`.** 10 of 27 are case lemmas: 7 pass the foreign
       `EdgeRelation` to `simp`, 2 use `cases`/`fin_cases` + `rfl`, and `syntaxStep_eq` uses
       `fin_cases` + `rfl`. Even core definitions may not go to `simp` under COMMON §4.3. The
       module docstring's "proved by `rfl`/`Iff.rfl`" is inaccurate.
  - **The planned exit fails for the course file.** The 16 readers in the course file
    `ThreeSATToColoring.lean` cannot move to their owner under Q-H12-3 A, which keeps that file
    read-only even for two declarations. The bridge's "delete after owner PRs" exit is not
    available for them without a new ruling (R2).
  - **The quarantine is by convention only.** `Bridge` is public and re-exported by the
    `LevinHardness` facade, `ZeroKnowledge.lean` and the root.
  - **Fix.** Per R1/R2. Under R1 (A), these landing edits:
    - correct the docstring (case lemmas, which owner files);
    - replace "user ruling" in the three docstrings by the records reference of the ruling;
    - add a ledger/exception row with its repayment.
- **EFH12-F02 (major; small landing edit; R3). UnaryArith restates and re-derives public
  EncodingMachines rows.**
  - **What it is.** `unaryPow_poly` is an undisclosed re-derivation of a specialization of
    `EncodingMachines.unaryPolyOf_poly`. `unaryDiv_poly`/`unaryMod_poly` are new-name restatements
    of `divNum_poly`/`modNum_poly` with `divNum_eq`/`modNum_eq`; they are disclosed in the module
    docstring but missing from REPORT § *Overlap*.
  - **Precedents.** G45-01 and G48-01: an undisclosed re-proof or restatement of a public lemma is
    graded major.
  - **Fix** (R3 A):
    - derive `unaryPow_poly` from `unaryPolyOf_poly (.pow .var n) hf` by `PolyExpr.eval_pow` (one
      line), or delete it and use `unaryPolyOf_poly` at its call sites;
    - record div/mod and the FormulaKit triplication in the ledger.
- **EFH12-F03 (minor; CLOSED by phase 2). Seal evidence is partial.**
  - **Variants not run.** Only the strict whole-file seal was run; canonical coe-A and seal B were
    not. The worker says these variants "are not among my inputs". In fact the gate-04 tools in
    its own `evidence/tools/gate04-seal-tools/` are byte-identical to the records'
    `gates/04-s2b/evidence-r5/tools/` (33 of 34 files; only `mods.txt` differs), and COMMON C6
    names that method.
  - **No raw logs.** Raw Lean logs of the seal runs are not kept, as in EF-D1.
  - **Over-broad unseals.** 9 bridge declarations unseal more than their named definition:
    - `toCNF_eq` (+`tseitinGates`);
    - `decode_eq` (+`fallback`, `parse`);
    - `serialize_eq` (+`serializeClause`);
    - `serializeClause_eq` (+`serializeLit`);
    - `syntaxOK_eq` (+`syntaxStep`);
    - `satisfiesClause_eq` (+`SatisfiesLiteral`);
    - `satisfiesSat3_eq` (+`SatisfiesClause`);
    - `isSatisfiable_iff` (+`SatisfiesSat3`);
    - `reductionGraph_adj` (+`EdgeRelation`).

    So "unsealed for exactly its own target" is not shown.
  - **Thin controls.** There are 9 control pairs for about 50 new public definitions.
  - **Phase 2 closes every point:**
    - canonical coe-A and seal B were run on the 11 owners, with raw logs kept;
    - with each of the 27 bridge declarations unsealed for only its named definition, all 27
      compile, so none of the 9 extra unseals is needed;
    - 50 control pairs, one per new public definition, are ALL_OK.

    The canonical seal also found **F08**.
- **EFH12-F04 (minor; CLOSED by phase 2). C2 is incomplete.** The root `TCSlib` was not built, and
  `audits/pass-shelat/Checks.lean`, which imports `TCSlib.Cryptography.ZeroKnowledge`, is
  missing from REPORT's importer list.
  - **Phase 2:** the root and `audits/pass-shelat/Checks` are rc 0 with 0 errors, among the
    predicted 16 modules.
- **EFH12-F05 (minor; PARTLY CLOSED by phase 2: (a) and (b) closed; (c) is a landing edit; (d)
  stays on record). Stale evidence and text:**
  - **(a)** The C12 probe ran at `0c95b0b9` (commit 12). `Gadget.lean` and `ColoringWitness.lean`
    changed afterwards. *Closed:* `ProbeH12.lean` passes at the check head, with rc 0 and 0 errors.
  - **(b)** C10 counted 244 new constants, before `verTime_eq`. *Closed as evidence:* the phase-2
    census covers all 245, and their axiom sets equal `stmtdump.txt`.
  - **(c)** The `CircuitWitness.lean` module docstring still says `R_3SAT_wireValues` "takes [the
    `toCNF` equation] as the hypothesis" ("given the equation of the Tseitin formula"). It now uses
    `Bridge.toCNF_eq` and has no such hypothesis.
  - **(d)** The top-level `SHA256SUMS` omits `evidence/SHA256SUMS`.
- **EFH12-F08 (minor, new in phase 2; landing edit LE-h12-strip). A definitional read of a foreign
  matcher in `polyTimeComputable_stripCert` (`Verifier.lean:131-134`).**
  - **What it is.** The proof checks `stripCert` against the catalog function of
    `Turing.FinTM.computesFunInTime_stripLast` by defeq. That needs the compiler-generated foreign
    matcher `Turing.FinTM.stripLastTM_computes.match_1`.
  - **Evidence.** This is the only failure of the canonical coe-A seal, and of seal B. The worker's
    strict seal did not include matchers, which is why it passed. With only that matcher sealed, the
    proof fails the same way.
  - **Precedent.** dl-c's `dlc_ssLoop_poly`: minor, not a Rule-10 violation in substance, but
    avoidable.
  - **Fix.** Transport along `stripCert_eq` and `split` both matches. This compiles with the matcher
    and `stripCert` sealed (phase 2 `StripProbe` F1/F3).
  - **Before landing:** check that the fix goes through the splitter and equation lemmas, not
    constructor-discriminant reduction of the sealed matcher (the cleanup "N4 boundary"), and re-run
    the canonical seal of `Verifier`.
- **EFH12-F06 (minor; disclosure, for the ledger). Near-relatives missing from REPORT § *Overlap*,
  none a public re-proof:**
  - `polyTimeComputable_syntaxOK` is statement-identical to the private `satSyntax_poly`
    (`SAT.lean:306`);
  - `polyTimeComputable_foldl_accept` is the public form of the private
    `satScanTM`/`satScan_computes`;
  - `unaryDivConst_poly`/`unaryModConst_poly` relate to the private `clA5Div_native`/`clA5Mod_native`.
- **EFH12-F07 (minor; attribution wording). Two anchors stretch the brief's list:**
  - `[AB09, §2.3.1]` (on `R_3SAT`) is not on the brief's list. It is, however, an anchor of the
    audited `Formulas/CNF.lean` ("[AB09, §2.3.1]'s `k`CNF"), so it is not fabricated.
  - Module references "(§2.3.)" appear on glue-only files (`UnaryArith`, `Gadget`, `Padding`) and
    on the 3SAT → 3COL files.
  - `NP.lean` uses `[AB09, §2.3]` for Levin reductions. Used as "the Levin reduction … ([AB09,
    §2.3])", that is acceptable; on unary arithmetic rows it is not.
  - Otherwise, only the brief's anchors are cited: [AB09] Def 6.9, Lemmas 6.10/6.11 p. 111,
    Remark 6.7, §2.3; [PS10] §4.7, Theorem 124.1 step 2, Definition 191.11.
  - No quotation is used. Garey–Johnson and Stockmeyer are not cited, and §2.3.6 is not used.
  - The final citation gate waits for the Q-H12-2 ingestion (R4).
- **EFH12-I1 (information).** H12-P1 (string-level `#eval`) was not run: `tabEmit` is
  `noncomputable`, and the instance is far beyond kernel `decide`. H12-P2 is replaced by the proved
  field `length_eq` for every `x`, which is stronger. Accepted deviation.
- **EFH12-I2 (information).** `polyTimeComputable_colorInst_of` is a public conditional form: its
  hypotheses are the poly-time of `memS`/`goodS`. It is discharged by the unconditional
  `polyTimeComputable_colorInst`. It is not smuggling, but it could be made private at landing.
- **EFH12-I3 (information).** Readers were handled inconsistently across two J6 files:
  `Graph.ofSimpleGraph` (`ThreeColoring/Language.lean`) was routed around with a restated lemma,
  while `LevinNPHard` (`NP.lean`) was bridged. This is only a note for R1 (B).
- **EFH12-I4 (information).** Commits 1–3 have the author "Claude (EF-H12 fill)" and commits 4–19
  "Claude-EF-H12". All carry the worker's `Claude-Session` trailer
  (`session_01PqpVTiM56gUi2Nwh8ya4ah`). Keep them verbatim in cherry-picks, as in earlier
  landings.
- **EFH12-I5 (information).** The worker's questions are relayed in R1 (W1), R3 (W2) and R5 (W3).
- **EFH12-I6 (information).** Merge preview:
  - `git merge-tree --write-tree c8d5b3c7 bff0567b` is clean, giving tree
    `efdd41d867a0d057d7fce00b915aedcc743138f3`.
  - REC is an ancestor of `bff0567b`.
  - The 12 Lean paths `bff0567b` changes (GSW/LWE) are **outside** the 302-module TCSlib import
    closure of the changed facade, so snapshot #11 covers the whole closure.
  - *Confirmed in phase 2:* `git am` of the 19 patches on `bff0567b` gives tree `efdd41d8…`, and
    `stateplan` rebuilds exactly 16 modules while reusing 1453.

## Phase 2 plan (one Lean process, when a slot frees; snapshots.md job recipe, as EF-D1 `phase2.md`)

*Executed on 2026-11-18. The results are in [`phase2.md`](phase2.md), step by step.*

- **Deviation: one coe-A and seal-B failure (F08).**
- **Additions beyond the plan:**
  - a no-unseal bridge control, which shows the 7 `simp` readers need no unseal;
  - an attribution and fix probe for F08.

`$SP` = `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.

**P2-0 Inputs.**
- **Records tip.** It must be Lean-equal to `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d`. At review
  time, the tip `6d191bb8` gives an empty `git diff --name-only bff0567b HEAD` over `TCSlib`,
  `TCSlib.lean`, `audits`, the lake files and `lean-toolchain`.
- **Snapshot #11.** `$SP/olean-snapshot`:
  - map `olean-snapshot.map-bff0567b.tsv` = `e7bb03b4…867d0`;
  - files `olean-snapshot.files-bff0567b.txt` = `463c8869…0b13` (both re-hashed at review time);
  - rehash 0/0/0 before, after the build and at the end.
- **Recipe tools.** The same unmodified set as EF-D1 (`olean-advance-a6d01b1b/tools-used/` from
  `olean-rebase-evidence.zip`), plus `seal/review/{mkcollect,mkseals_coe,sealsum}.py`.

**P2-1 Scratch merge and check head (scratch only, never pushed).**
- Make a sparse detached worktree at `bff0567b`.
- Apply the 19 patches with `git am`, unsigned (or `git merge --no-ff c8d5b3c7`).
- The expected **tree** is `efdd41d867a0d057d7fce00b915aedcc743138f3`.
- Against `bff0567b`, exactly the 14 delivery paths change (+4,000).

**P2-2 Replay.**
- `cp -al $SP/olean-snapshot $SP/olean-replay-efh12` (hard links only; the snapshot is never
  written), then `mloverlay.sh`, and `mathlibextra.sh` if the plan asks.
- Run `stateplan init` at `bff0567b`, then `downorder.py`. The expected **changed** set is 14:
  the 13 new modules and `TCSlib.Cryptography.ZeroKnowledge`.
- Expected **down** set: `TCSlib` (root) and `audits/pass-shelat/Checks`.
  `audits/garg-ch1-3/Checks` does not import ZeroKnowledge and is reused.
- **Expected build set: 16 modules, everything else reused.** In import order:
  1. `LevinHardness.{Relations, Bridge, Gadget, Padding}` (independent);
  2. `UnaryArith` (needs Gadget);
  3. `Verifier` (needs Relations);
  4. `CircuitWitness` (Relations, Bridge);
  5. `ColoringGraph` (Gadget, Relations, UnaryArith);
  6. `ColoringWitness` (UnaryArith);
  7. `ColoringParse` and `Soundness` (ColoringGraph, Bridge);
  8. `Hardness`;
  9. the `LevinHardness` facade;
  10. the `ZeroKnowledge` facade;
  11. `TCSlib`;
  12. `audits/pass-shelat/Checks`.
- **Pass:** 16/16 rc 0, 0 `error:`/`error(`, 0 `sorry`, `permod.py` clean. The delivery sources
  in the export must equal `src/`. This closes F04.

**P2-3 Axioms.**
- Run `#print axioms` independently on all 245 new constants, the headline and both corollaries:
  each within `propext`/`Classical.choice`/`Quot.sound`.
- Add a `sorry` control that is flagged.
- Expected for the headline: `[propext, Quot.sound, Classical.choice]`.

**P2-4 Seals.** The new files are the owners of the reading declarations.
- **Canonical coe-A** on the 11 non-bridge files: Relations, Verifier, CircuitWitness, Gadget,
  UnaryArith, ColoringGraph, ColoringParse, ColoringWitness, Soundness, Padding, Hardness.
  Expected 0 errors. Strict and seal-B variants are run and attributed.
- The sealed definitions are owned by:
  - the five **bridged owners**: `Formulas/CNF`, `Formulas/CNFEncoding`,
    `CircuitComplexity/DAGCircuitSat`, `NPReductions/ThreeSATToColoring`, `ZeroKnowledge/NP`;
  - the rest of the candidate set:
    - `CircuitComplexity/{DAGCircuit, DAGCircuitSatLang, Uniform, UnaryCode, UniformTableauSpec,
      UniformTableauEmitterMain, CircuitEvalSpec, CircuitEvalMachine}`;
    - `ClassNP/{PolyTime, PolyTimePairing, PolyTimePrefix, Transducer, NP}`;
    - `ClassP/{P, BinaryArith/Loops}`;
    - `TuringMachine/{Encoding, Finite, Build/Convention}`;
    - `Randomized/PolyExpr`, `CookLevin/Snapshot`;
    - `ZeroKnowledge/{Encoding, EncodingMachines, Defs, ThreeColoring/Language,
      ThreeColoring/Protocol}`;
    - `Asymptotic/{OneWay, HardCore/Functions}`.
- **`Bridge.lean`, minimal unseal (closes part of F03).** Each of the 27 declarations is unsealed
  for **only** the definition it is named for. Any declaration that then fails is listed with the
  extra name it needs.
- **Controls.** Extend the paired controls to every new public definition (about 50), as EF-D1 did:
  each NEG fails exactly once and each POS passes.
- Run the gate-04 explicit-unfold scan (`scan.py`).

**P2-5 Bridge demonstrations (for R1).**
1. **Necessity.** With the bridged definitions sealed and the bridge readers removed, `Soundness`,
   `ColoringParse`, `CircuitWitness` and `Hardness` fail at the reader uses.
2. **Owner form.** The 27 readers compile verbatim as an overlay appended to their 5 owner files
   on a scratch tree. This gives the text of any owner PR. They are not committed.

**P2-6 Landing-edit probes.**
- **F02:** `unaryPow_poly` from `unaryPolyOf_poly (.pow .var n) hf` compiles, and its downstream
  rebuilds.
- **F05a:** re-run `evidence/probes/ProbeH12.lean` at the check head.

**P2-7 Lint** on the merged tree: 92 FAIL / 103 WARN with unchanged line sets.

**P2-8 Records.** Write `phase2.md` and the evidence zip with `PROVENANCE.txt`, beside this file.

## Landing (if R1 is A)

- **Branch.** `land/ef-h12-levin-3col`: `bff0567b` plus maintainer cherry-picks of the 19 commits,
  plus the landing edits:
  - **LE-h12-pow** (F02);
  - **LE-h12-doc**: F01 docstrings, F05c and the F07 wording;
  - **LE-h12-strip** (F08, added after phase 2): `polyTimeComputable_stripCert` by transport along
    `stripCert_eq`. Its proof term is checked against the N4 boundary, and the canonical seal of
    `Verifier` is re-run;
  - optionally **LE-h12-priv** (I2).
- **The PR.** A draft PR on the records branch. It leaves draft after phase 2 passes, R1–R4 are
  answered, and the Codex gate (Q-H12-2 A: citations after ingestion) closes.

## Questions for Seyoon (recommended option first)

- **EF-H12-R1 (confirm or replace the reported "Readers in our files" ruling; worker question
  W1).** The worker reports that you ruled "Readers in our files" on its E-SCOPE. The records have
  no such ruling. As delivered, `Bridge.lean` states:
  - 27 readers of definitions in 5 frozen owner files: `Formulas/CNF`, `Formulas/CNFEncoding`,
    `DAGCircuitSat`, the course file `ThreeSATToColoring`, and the J6 file `ZeroKnowledge/NP.lean`
    (the last added after checkpoint 1);
  - 17 by `rfl`/`Iff.rfl` and 10 as case lemmas, 7 of which pass `EdgeRelation` to `simp`.

  Did you rule this, and does it cover all 27?

  *Facts established by phase 2 (no ruling implied):*
  - **Minimal unseal.** Each of 20 readers compiles with only its named definition unsealed, and
    fails with none. The 7 `simp [EdgeRelation]` readers compile with `EdgeRelation` **sealed**:
    they read it through its equation lemmas, which a seal cannot block. Only the explicit-unfold
    scan sees them (7 hits, all in `Bridge.lean`).
  - **Necessity.** With the bridged definitions sealed and each reader use proved in place, all 46
    uses in `CircuitWitness`, `ColoringParse`, `Soundness` and `Hardness` fail.
  - **Owner form.** The 27 readers compile verbatim appended to their 5 owner files, with no added
    import.
  - **(A, recommended)** Yes: confirm it as a **bounded, recorded Rule-10 exception** for exactly
    these 27 readers.
    - Landing edits:
      - the bridge docstring states which readers are case lemmas;
      - "user ruling" in three docstrings is replaced by the decision-log reference.
    - A ledger row records the repayment:
      - the 11 Complexity readers move to their owners in one reader-only PR at the next
        Arora–Barak window;
      - `levinNPHard_iff` moves into `NP.lean` after Stage 2 lands (it is a Stage 2 owner file);
      - the 16 course-file readers follow R2.
    - *Why:* the headline cannot be stated or proved through sealed definitions without readers.
      The bridge is small, all-`rfl` apart from the case lemmas, and checkable mechanically (P2-5).
  - (B) Confirm only for the Complexity and course files. Move `levinNPHard_iff` into `NP.lean`
    now, as a one-line landing edit coordinated with Stage 2 (S2-A owns proof-level rows there).
  - (C) Not confirmed: the owner reader PRs land first (reader-only additions to the 4 Complexity
    files, the course file and `NP.lean`). Then `Bridge.lean` is deleted and its consumers are
    re-pointed before this lands.
  - (D) Not confirmed and no owner change: the E-SCOPE stands, and the headline does not land.
- **EF-H12-R2 (the course file `ThreeSATToColoring.lean`; interacts with Q-H12-3 A).** 16 of the
  readers, and the re-derived colouring, exist only because the course file is read-only.
  - **(A, recommended)** Keep the course file read-only, as ruled in Q-H12-3 A. Its 16 readers
    stay in `Bridge.lean` permanently, as a recorded exception for course material.
  - (B) Lift read-only for one reader-only owner PR in the course file: the 16 readers, plus
    making `sat3Coloring` public with its properness lemma. Then delete the bridge's course
    section, and drop the re-derived `gadgetNodeColor` properness proof (overlap (b)).
- **EF-H12-R3 (UnaryArith duplication, F02; worker question W2).**
  - **(A, recommended)** Landing edit: `unaryPow_poly` is derived from `unaryPolyOf_poly` (or
    removed). `unaryDiv_poly`/`unaryMod_poly` stay as disclosed `/`-form corollaries of
    `divNum_poly`/`modNum_poly`, with a ledger row. The sorried FormulaKit rows
    (`Emit.lean:216-271`) are queued for their owner (W2 A).
  - (B) Remove `unaryDiv_poly`/`unaryMod_poly`/`unaryPow_poly`; the call sites use `divNum_poly` +
    `divNum_eq` and `unaryPolyOf_poly` directly.
  - (C) Accept as delivered, disclosure only.

  *Fact established by phase 2:* the LE-h12-pow form
  (`simpa only [PolyExpr.eval_pow, PolyExpr.eval_var] using unaryPolyOf_poly (.pow .var n) hf`)
  compiles, and its 10-module downstream rebuilds with rc 0.
- **EF-H12-R4 (Q-H12-2 A is still pending: [AB09] ch. 2 and 6 and a 3-colouring source are not
  ingested).**
  - **(A, recommended)** Phase 2 and the landing branch proceed now. The ingestion happens before
    the PR leaves draft, and the citation check (F07 included) is re-run against the ingested
    text in the Codex gate.
    - Per rule 16, the ingestion needs from your machine the [AB09] PDF (chapters 2 and 6) and
      one 3-colouring source ([GJ79, App. A1.1, GT4] or [Sto73]).
    - The maintainer's ingestion message will give the exact file names, their SHA-256 values and
      the staging commands before the job.
  - (B) Hold the review at phase 1 until the ingestion is done (the literal order of Q-H12-2 A).
- **EF-H12-R5 (worker question W3: promote `polyTimeComputable_foldl_accept`).**
  - **(A, recommended)** Yes: record it as a registered host row (finite-automaton verdict; it
    instantiates `polyTimeComputable_transduce` and is the public form of `SAT.lean`'s private
    scan). The duplication with that private scan goes in the ledger.
  - (B) Keep it local to EF-H12.

**Not yet clear to merge — phase 2 passed (ACCEPT WITH LANDING EDITS, new minor F08); EF-H12-R1 (the
unconfirmed "Readers in our files" ruling) and R2–R5 open; landing branch (with LE-h12-pow,
LE-h12-doc and LE-h12-strip) not yet made; Q-H12-2 ingestion pending.**
