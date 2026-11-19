# Gate 57 · EF-H12, `LevinNPHard L3COL R3COL`: PR #398, with the source review of four reference ingests · round 1

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). **Gate 57** has
two parts:
1. **The audit of draft PR #398** (efficiency wave 1, job EF-H12 `ef-h12-levin-3col`). It proves
   `LevinNPHard L3COL R3COL` with no hypothesis, and with it the two ZK-for-NP theorems of [PS10, Theorem 124.1] lose
   their `LevinNPHard` hypothesis. The maintainer reviewed it in house (phase 1 static, phase 2 Lean replay: ACCEPT
   WITH LANDING EDITS) and landed it with four landing edits. It has had no external audit.
2. **The Codex source review** of the reference ingests made for it: [AB09] ch. 2 and ch. 6, [GJS74] and [St73]
   (`blueprint/src/references/`). All four pairs are marked "awaiting Codex source review"; their anchors may not be
   cited by `\statementsource`/`\proofsource` until this review passes them. Ruling EF-H12-R4 (A) put this check, and
   the re-run of the citation check (finding EFH12-F07 included), in this gate.

| Item | Value |
|---|---|
| PR | **#398**, draft, `land/ef-h12-levin-3col` → `cryptography/pass-shelat-ch2-4` |
| Head | **`11f33ef370efe39dc62c958b99836df0d874b18f`** (`TCSlib` tree `af61c838…`) |
| Base (= merge base with the records tip) | `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d` (`TCSlib` tree `949dfd63…`) |
| Commits · diff | 23 · 14 files, +4,068/−0: 13 new files under `ZeroKnowledge/LevinHardness/` and the facade `ZeroKnowledge.lean` (+7) |
| Worker commits 1–19 | the delivery's 19 patches, applied with `git am -3 -S`; head `393c5cc1f1690114bb52cae031c3d71a24c6bf9c`, tree `efdd41d8…` (= phase 2's check head) |
| Landing edits 20–23 | `4230f872fff33da4e8ce4b47906b4a0df6774c36` **LE-h12-arith**, `76676c145a8004a2451d55654e79a61e31881ec7` **LE-h12-strip**, `ad07b07c4eeca3cda93312c04448b39925cd1669` **LE-h12-bridge**, `11f33ef3` **LE-h12-doc** |
| Delivery | `exchange/pass-shelat-ch5-8` at `36d9ac03c329544d33b1f3f9a73e6ce32152dde2`, folder `inbox/fills/ef-h12-levin-3col/` (`REPORT.md`, 19 patches, `src/`, `evidence/`) |

**The diffs** in this directory:
- `pr398.diff.txt`: `bff0567b..11f33ef3` (the PR; GitHub's three-dot view, since the base is the merge base);
- `le-arith.diff.txt`: `393c5cc1..4230f872`;
- `le-strip.diff.txt`: `4230f872..76676c14`;
- `le-bridge.diff.txt`: `76676c14..ad07b07c`;
- `le-doc.diff.txt`: `ad07b07c..11f33ef3`.

**Records pin:** the commit that files this directory, `briefs/pass-shelat-ch5-8/gates/57-ef-h12-levin-3col/`.
- **The records tip at staging** is `56df3925884cfba6ec043f0aa3abe0ed64e466ca`, `TCSlib` tree
  `745bf4b494b6581a5666ef9ca0a6e735a68ddcef`. The pin is records-only on top of it.
- **The landing re-check** merged the head with records `fb57a36c`, whose `TCSlib` tree is the same `745bf4b4…`. Since
  then the records side changed 0 paths under `TCSlib/`, `TCSlib.lean`, `audits/`, `scripts/`, the toolchain, the
  manifest or the lakefile.
- **Since the PR base,** the records side changed 2 Lean paths: `GSW/Branching` and `GSW/DecryptFormula` (U12/U13,
  #392). Neither is in the PR.

**Merged tree:**
- `git merge-tree --write-tree 56df3925 11f33ef3` is clean: tree `7a7e92293aee9287ac51bd4d6f6bba897876c8b3`, `TCSlib`
  tree **`05b0eecda079cda320090f0581b623ef38e898b8`**. The merge with `fb57a36c` has the same `TCSlib` tree.
- The landing replayed it as the scratch commit `a3617cde18766131a63c5f0b766a073d4863f832` (parents `11f33ef3` and
  `fb57a36c`; tree `d55035ca…`; **on no ref, never pushed**).

**Mathlib** `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, **Batteries** `39260e31b7b3f7f05643da95242463b462dc05f1`,
toolchain `leanprover/lean4:v4.25.0` (the PR does not change the manifest).

Paths below are under `TCSlib/Cryptography/ZeroKnowledge/LevinHardness/` unless they start with `TCSlib/`,
`briefs/` or `blueprint/`. Line numbers are at the PR head.

## How this gate runs (standing rules 16, 17 and 18)

- **Cloud, reading only.** Every repository input is on the records branch at the pin, the PR branch, and the exchange
  branch (the delivery). The only inputs from Seyoon's machine are the **three source PDFs, attached to the Codex
  task** (the dispatch lists their names and SHA-256). They are never committed (policy; pairing Q12 A).
- **No Lean, no cache.** The auditor does not run `lean`, `lake` or `lake exe cache get`, and builds nothing. The build
  evidence is the maintainer's: phase 2 (`briefs/efficiency-gaps/wave1/EF-H12/final-r1/phase2.md` and its ZIP), the
  landing re-check (`landing.md`), and this directory's packaging of it (`verification-r1.md`, `verification-r1.zip`).
  The audit grades that evidence by reading it.
- **Tools:** Python as `python3 -I`; `git`, `sha256sum`, `unzip`, a PDF reader or `pdftotext`/`pypdf` for the attached
  PDFs, and reading tools only. Mathlib and Batteries source may be read at the pinned revisions, never built.
- **Sources.**

  | Status | Sources |
  |---|---|
  | Ingested, **under review in this gate** (the attached PDF is the authority) | **AB09** ch. 2 (`arora-barak-ch02-np-completeness.{md,raw.md}`, 98 blocks, PDF pp. 55–80) and ch. 6 (`arora-barak-ch06-circuits.{md,raw.md}`, 59 blocks, PDF pp. 117–130), the authors' web draft `book.pdf`; **GJS74** (`garey-johnson-stockmeyer-1974-simplified-np-complete.{md,raw.md}`, 25 blocks); **St73** (`stockmeyer-1973-planar-3-colorability.{md,raw.md}`, 20 blocks) |
  | Ingested earlier (not under review here) | **PS10** ch. 4 (`pass-shelat-2010-ch4.raw.md`: Theorem 124.1, l. 646) and the appendix (Definition 191.11) |
  | Not ingested | the AB09 **CUP 2009** edition (TCSlib's numbers are CUP numbers; only the draft is ingested); [GJ79]; the CS 294-268 course material (cited through the Lean file `TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean`) |

  A finding that depends on the wording of a source that is neither ingested nor attached is marked
  **UNVERIFIED-SOURCE**. If a PDF is missing from the chat, say so and mark the findings that need it
  UNVERIFIED-SOURCE.

## Scope

### Part 1 · PR #398

| File | Lines | Content |
|---|---:|---|
| `Relations` | 78 | `R_CKT` (`:56`), `R_3SAT` (`:69`) with readers |
| `Bridge` | 240 | **the recorded Rule-10 exception**: 27 readers of foreign definitions (below) |
| `Verifier` | 358 | step 1: `certOf` (`:85`), `stripCert` (`:112`), `polyTimeComputable_stripCert` (`:138`, LE-h12-strip), `verTest` (`:161`), `verTime` (`:218`), `tabInst` (`:252`), `exists_tabReduction` (`:316`) |
| `CircuitWitness` | 426 | step 2: `wireValues` (`:268`), `R_3SAT_wireValues` (`:385`), `exists_R_3SAT_iff` (`:417`) |
| `Gadget` | 191 | the gadget graph on `Fin (gadgetN K)`, `gadgetGraph` (`:184`) |
| `UnaryArith` | 92 | `unaryDivConst_poly`, `unaryModConst_poly`, `clauseLit_poly`, `litVal_poly` (after LE-h12-arith) |
| `ColoringGraph` | 675 | step 3: `colorInst` (`:271`), `polyTimeComputable_colorInst_of` (`:382`), `threeColorable_gadgetGraph_iff` (`:441`) |
| `ColoringParse` | 720 | step 3's tests: `polyTimeComputable_foldl_accept` (`:108`, DL-64), `polyTimeComputable_syntaxOK` (`:121`), `polyTimeComputable_colorInst` (`:717`) |
| `ColoringWitness` | 400 | step 4: `gadgetNodeColor` (`:71`), `gadgetColor` (`:98`), `properColoring_gadgetColor` (`:214`), `colorWord` (`:240`) |
| `Soundness` | 259 | the course theorem `SATtoColorReduction` transported along a graph homomorphism (not re-proved) |
| `Padding` | 250 | `padGraph` (`:59`), `padWord` (`:114`), `padColWord` (`:196`) |
| `Hardness` | 313 | `exists_R_3SAT_iff_padWord` (`:167`), `R3COL_padWord` (`:181`), **`levinNPHard_L3COL`** (`:230`), the two `…_unconditional` corollaries (`:286`, `:302`) |
| `LevinHardness.lean` (facade) | 59 | imports and module text |
| `TCSlib/Cryptography/ZeroKnowledge.lean` | +7 | one import, a `## Contents` bullet, the [St73] References entry |

**The headline.** `levinNPHard_L3COL : LevinNPHard L3COL R3COL`, no hypothesis. `LevinNPHard` and `LevinReduction`
are `TCSlib/Cryptography/ZeroKnowledge/NP.lean:654` and `:134`: polynomial-time `f`, polynomial-time `w` on `⟨x, y⟩`,
`x ∈ L ↔ f x ∈ L'`, `R x y → R' (f x) (w x y)`, `|f x| = p(|x|)` for every `x`, and `N ≤ p(N)`. The reduction built
is `f x = padWord (colorInst (dagCktSatToSAT3 (f₁ x))) B(|x|)`, `w x y = padColWord (colorWord … (wireValues (f₁ x)
(certOf q x y))) B(|x|)`, `p = B·B`, `B(n) = A(n+1)^a + n + 1`. The corollaries restate the conclusions of
`zk_proof_of_witnessRelation_of_owp` (`NP.lean:689`) and `zk_proof_of_mem_NP_of_owp` (`:742`) without the hypothesis.

**`Bridge.lean`: exactly 27 readers** (ruling EF-H12-R1 (A), ledger DL-65):

| Owner file | Readers | Proofs |
|---|---|---|
| `TCSlib/Complexity/Formulas/CNF.lean` | `widthAtMost_iff`, `numVars_eq` (2) | `Iff.rfl`, `rfl` |
| `TCSlib/Complexity/Formulas/CNFEncoding.lean` | `serializeLit_eq`, `serializeClause_eq`, `serialize_eq`, `decode_eq`, `fallback_eq`, `syntaxStep_eq`, `syntaxOK_eq` (7) | `rfl`; `syntaxStep_eq` is a case lemma (`fin_cases`/`cases`, `rfl`) |
| `TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean` | `toCNF_eq` (1) | `rfl` |
| `TCSlib/Cryptography/ZeroKnowledge/NP.lean` | `levinNPHard_iff` (1) | `Iff.rfl` |
| `TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean` (course) | `satisfiesLiteral_pos/_neg`, `satisfiesClause_eq`, `satisfiesSat3_eq`, `isSatisfiable_iff`, `is3Colorable_iff`, `reductionGraph_adj` (7) and the nine `edgeRelation_*` case lemmas (16) | 7 `rfl`/`Iff.rfl`; `edgeRelation_literal_gadget`/`_gadget_literal` by `cases`/`fin_cases` and `rfl`; the other seven by `simp [EdgeRelation]` |

10 + 1 + 16 = 27; 17 are `rfl`/`Iff.rfl` and 10 are case lemmas.

**The landing edits** (`landing.md` § *Landing edits*):
- **LE-h12-arith** (EFH12-F02, EF-H12-R3 (B)): `unaryPow_poly`, `unaryDiv_poly`, `unaryMod_poly` deleted; call sites use
  `EncodingMachines.unaryPolyOf_poly (.pow .var k)` with `PolyExpr.eval_pow`/`eval_var`, and `divNum_poly`/`modNum_poly`
  with `divNum_eq`/`modNum_eq`. Code in `UnaryArith`, `ColoringGraph`; +32/−45.
- **LE-h12-strip** (EFH12-F08): `polyTimeComputable_stripCert` transports `computesFunInTime_stripLast` along a
  pointwise equality, rewriting the inner `match` by `Turing.FinTM.stripLastTM_computes.match_1.eq_1`/`eq_2`; a proof
  sketch added; statement unchanged. +25/−2.
- **LE-h12-bridge** (EFH12-F01, EF-H12-R1 (A)): docstrings only, 3 files, +45/−28.
- **LE-h12-doc** (EFH12-F05(c), F07 (a)–(c), [St73] F1–F4, F6): docstrings only, 9 files, +65/−24.
- **LE-h12-priv** (EFH12-I2, optional) was **not** done (pack S-6).

**Out of scope** (mention only if something in scope depends on it): the owner PRs that repay the bridge (Complexity
readers, the course file per EF-H12-R2 (B), `levinNPHard_iff` after #390); Stage 2 (#390) and `NP.lean` itself; the
records side of the merge (GSW U12/U13); the FormulaKit owner work; EF-D4 and the other wave-1 jobs.

### Part 2 · the source review

| Pair (`blueprint/src/references/`) | Source PDF (attached) | Report |
|---|---|---|
| `arora-barak-ch02-np-completeness.{md,raw.md}` | `book.pdf`, PDF pp. 55–80 (printed draft pp. 39–64) | `briefs/efficiency-gaps/wave1/EF-H12/ingest-report.md` |
| `arora-barak-ch06-circuits.{md,raw.md}` | `book.pdf`, PDF pp. 117–130 (printed draft pp. 101–114) | the same |
| `garey-johnson-stockmeyer-1974-simplified-np-complete.{md,raw.md}` | `gjs74.pdf`, 17 pp. (printed 47–63) | `…/EF-H12/ingest-report-gjs74.md` (its R1–R6 are superseded by the St73 report's F1–F6) |
| `stockmeyer-1973-planar-3-colorability.{md,raw.md}` | `st73.pdf`, 7 pp. (printed 19–25) | `…/EF-H12/ingest-report-st73.md` |

Also `blueprint/src/references/sources.json`: tags `AB09` (its `documents` gained the ch02 and ch06 names), `GJS74`,
`St73`.

## Rulings and records in force

1. **Rule 15** (`briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2): every honest algorithm is proved efficient
   **uniformly** (`PolyTimeComputable`, or `∃ A, A.Uniform ∧ A.Computes f`; never a bare `∃ A : NUPPT, A.Computes f`);
   a missing efficiency proof is at least a major. Here: every instance and witness map.
2. **The EF-H12 contract:** `briefs/efficiency-gaps/wave1/EF-H12/brief.md` (route, targets, the disclosed overlaps
   (a)–(c), must-reuse list) and `briefs/efficiency-gaps/wave1/COMMON.md` §4.3 ("A missing reader is a scope request,
   never an unfold"). Rulings Q-H12-1 (A) (the circuit route), Q-H12-2 (A) (ingest AB09 ch. 2/6 and a 3-colouring
   source), Q-H12-3 (A) (re-derive the colouring, disclosed) in `briefs/efficiency-gaps/wave1/rulings.md`.
3. **Decision-log rows** (`PassShelatChapter5-8Plan.md`, 2026-11-18/19): EF-H12 checkpoint 1; phase 1 review; phase 2
   passed; **EF-W1-R (A)** (readers go into their owner files); **EF-H12-R1 (A)** (land now with a bounded bridge);
   **R2 (B)** (one reader-only owner PR on the course file; then the bridge's course section and EF-H12's re-derived
   properness proof are dropped); **R3 (B)** (remove the three `UnaryArith` helpers); **R4 (A)** (proceed; ingest
   later; this gate re-runs the citation check); **R5 (A)** (`polyTimeComputable_foldl_accept` becomes a registered
   host); "EF-H12 sources"; "GJS74 ingested"; "AB09 ch. 2 and ch. 6 ingested"; "[St73] ingested"; "Course-file
   attribution ruled"; "EF-H12 landing started"; "EF-H12 landed as draft PR #398".
4. **Ledger** (`briefs/pass-shelat-ch5-8/duplication-ledger.md`): **DL-64** (`polyTimeComputable_foldl_accept` vs
   `ClassNP/SAT.lean`'s private `satScanTM`/`satScan_computes`; accepted, repay at the next Complexity window);
   **DL-65** (the bridge; accepted as bounded; repayment plan).
5. **Rule 10** (`policy.md` §1; R-04-5 (A), zero exclusions): another file's TCSlib definition is read only through
   published readers. The canonical **coe-A** seal (collected from the elaborated terms plus matchers) is the check; a
   seal does not see `simp [X]`/`unfold X`/`X.eq_N`, so the explicit-unfold scan is part of it; the N4 boundary is the
   cleanup's "through the splitter and equation lemmas, not by constructor reduction of a sealed matcher".
6. **Duplication** (`policy.md`; precedents G44-01, G45-01, G48-01): disclosure is not acceptance. **An undisclosed or
   unaccepted re-proof or restatement of a public TCSlib, Batteries or Mathlib lemma, including an inline
   re-derivation, is a major.**
7. **Policy** (`policy.md` §2–§3): formula docstrings with the statement prose first; a source tag with a precise
   location, or a glue statement; a deviation note where the statement departs from the source; a `## References`
   section per file; a `**Proof sketch.**` for every nontrivial proof; files of 150–600 lines as the target and under
   1,000.
8. **Ingest status.** An ingest marked "awaiting Codex source review" may not be cited by `\statementsource` or
   `\proofsource` until this review passes it (and an approved proofmatch run). The maintainer's dispositions for the
   AB09 numbering follow the ch07 precedent: **keep the CUP numbers in docstrings; record the draft mapping in the
   ingest.**

## Staging observations (the maintainer's, from staging and `verification-r1`)

The known items for grading. S-1 to S-6 are the landing report's own deviations and notes; S-7 and S-8 are the
review's open items; S-9 to S-13 were found at staging.

- **S-1 · the Complexity reader count: 10, not 11.** The EF-H12-R1 row, DL-65 and the landing dispatch say "the 11
  Complexity readers". The bridge has 10 readers of the three Complexity owner files (`CNF` 2, `CNFEncoding` 7,
  `DAGCircuitSat` 1); `levinNPHard_iff` is the 11th non-course reader. 10 + 1 + 16 = 27, as the docstring and the PR
  body say. The ruling's text and the ledger row were not corrected.
- **S-2 · LE-h12-strip names generated equation lemmas of a foreign matcher in source.** The proof writes
  `FinTM.stripLastTM_computes.match_1.eq_1`/`eq_2` (`Verifier.lean:138-156`). They are realised as private equation
  lemmas in `Verifier`'s environment; the canonical seal treats them as theorems; the explicit-unfold scan's rules do
  not list matcher equation lemmas. The N4 probe accepts the proof with the matcher axiomatized and rejects the
  delivered proof (`verification-r1.md` §7). The alternative (`split`/`simp`) reduces the matcher by defeq and fails
  N4. The clean fix named for later is an owner-side named function with a reader for `computesFunInTime_stripLast`.
- **S-3 · the private-matcher residual.** The catalog statement's **outer** `match` (on `pairDecode z`) elaborates to
  the **private** `Turing.FinTM.extract_run.match_1` of `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`
  (`computesFunInTime_stripLast`, `:3259`). The landing proof's `split` reduces it at constructors definitionally. No
  seal can name it from outside its file, and its equation lemmas cannot be named in source. With both matchers
  axiomatized, N4 rejects the landing proof. The delivered proof had the same residual. It is recorded as information
  for the Complexity owner, not fixed.
- **S-4 · key labelling in the landing replay.** `stateplan plan/build/update` ran keyed with the check head's
  **tree** id `d55035ca` instead of the commit `a3617cde`. The keys are source-content hashes; re-run at the commit:
  identical order, 0 to build, check 1,469/1,469 OK (`verification-r1.zip:replay/plan-commit/`,
  `stateplan-check-commit.log`).
- **S-5 · unused [AB09] References entries.** After F07 (c) dropped "(§2.3.)", `Gadget.lean` (`:59`) and
  `UnaryArith.lean` (`:40`) still list [AB09] under `## References` with no in-text [AB09] citation. `UnaryArith`'s
  only reference is that entry. The landing followed the disposition literally and named the drop as a gate item.
- **S-6 · LE-h12-priv not done.** `polyTimeComputable_colorInst_of` (`ColoringGraph.lean:382`), a public conditional
  form (hypotheses: poly-time of `memS`/`goodS`), stays public because `ColoringParse.lean:718` uses it; `private`
  would break that use.
- **S-7 · EFH12-F05(d) stays on record.** The delivery's top-level `SHA256SUMS` (1,683 rows) does not list
  `evidence/SHA256SUMS`, so the evidence manifest is not bound by the top level. Both manifests verify.
- **S-8 · the sorried FormulaKit rows are queued for their owner.** `TCSlib/Complexity/FormulaKit/Emit.lean:216-271`
  has `polyTimeComputable_unary_sub/_mul/_le/_div/_mod` as `sorry` and `_unary_pow` proved from the sorried `_mul`
  (EF-H12-R3 (B), worker question W2). EF-H12 does not use them (0 occurrences of `FormulaKit` in the 14 files).
- **S-9 · two slips in the landing record (no result changes).**
  - `landing.md` says seal B gives "each owner one more request". `Relations` has 191 requests in both variants (its
    closure does not contain `PolyExpr.eval`); the other 11 owners have one more.
  - `landing.md` says the worker's strict seal lines "do not name `divNum`/`modNum`, which `UnaryArith` and
    `ColoringGraph` now use". `UnaryArith`'s strict seal names both; `ColoringGraph`'s names neither
    (`verification-r1.zip:strict/strict-vs-head.txt`). The canonical coe-A seal requests both and gives 0 for both
    owners.
- **S-10 · overlap (b), the re-derived colouring.** `gadgetNodeColor`, `gadgetColor` and the properness theorem
  `properColoring_gadgetColor` are **public** (`ColoringWitness.lean:71`, `:98`, `:214`; the edge-case lemmas are
  private). DL-65 and EF-H12-R2 (B) call it "EF-H12's private re-derived properness proof", slated for removal when the
  course-file owner PR makes `sat3Coloring` public with its properness lemma. The arm-by-arm comparison with the
  course's `clauseGadgetColor`/`sat3Coloring` (`ThreeSATToColoring.lean:163-193`) was made in phase 1.
- **S-11 · near-relatives (EFH12-F06, for the ledger).** `polyTimeComputable_syntaxOK` is statement-identical to the
  private `satSyntax_poly` (`TCSlib/Complexity/ClassNP/SAT.lean:306`); `polyTimeComputable_foldl_accept` is the public
  form of the private `satScanTM`/`satScan_computes` (`:231`–`:295`; DL-64); `unaryDivConst_poly`/`unaryModConst_poly`
  relate to Cook–Levin's private `clA5Div_native`/`clA5Mod_native`. None is a public re-proof; F06 is "disclosure, for
  the ledger", and only DL-64 has a ledger row.
- **S-12 · stale docstrings outside the PR.** `NP.lean` says in four places that what this PR proves is not formalized:
  the module text (`:28-31`, "the string-level Levin reduction from `3SAT` is not formalized", and `:36-37`, "the
  padding is not formalized"), the `LevinReduction` docstring (`:131-132`, padding "should achieve it for `3COL`, with
  `p = q²`; not formalized") and the `LevinNPHard` docstring (`:652-653`). `NP.lean` is a Stage 2 owner file the PR may
  not edit; no follow-up records the update.
- **S-13 · the source-review items the ingest reports flag.**
  - **St73 page order:** printed pp. 20 and 22 are bound interchanged; the text runs 19 → 22 → 21 → 20 → 23, and the
    Theorem is on **p. 22** (`p004-b001`). The Lean citations rest on this ("Theorem, p. 22; proof pp. 21–22; Fig. 1,
    p. 24").
  - **Low-confidence St73 blocks:** Figure 2 `pdf-ecfb8ec9f7b3-p006-b003` (0.80: $G_C$, 19 nodes and 34 arcs read off
    the drawing, node letters the maintainer's) and Figure 4 `pdf-ecfb8ec9f7b3-p007-b002` (0.80); also Figure 1
    `p006-b002` and Figure 3 `p007-b001` (0.85). GJS74's Figure 1 `pdf-f17c4a237263-p007-b007` (0.85).
  - **AB09 numbering:** the ingest is the web draft. Ch. 2 is nearly aligned (draft Lemma 2.12/2.15 = CUP 2.11/2.14);
    ch. 6 differs (CUP §6.1.2, Def 6.9, Lemmas 6.10/6.11, p. 111 = draft §6.7, Def 6.30, Lemmas 6.31/6.32, printed
    p. 112; CUP "Remark 6.7" has no draft number). The docstrings keep the CUP numbers, which no ingested source can
    confirm.
  - **GJS74 locator:** "GRAPH 3-COLORABILITY is NP-complete, even for planar graphs" is §II, printed p. 52
    (`p006-b002`), stated and credited to [St73], with no proof. GJS74 is cited nowhere in Lean.
  - **Metadata not printed in the PDFs:** GJS74's venue, year and DOI; St73's volume, number and DOI. They come from the
    uploader's citations.
  - **Out of this PR, noted by the ingest:** `TCSlib/Complexity/CircuitComplexity/CircuitSatNPHard.lean`'s two quotes
    do not match the draft's wording; `sources.json`'s AB09 title names CUP 2009 while all four AB09 chapter files are
    draft ingests.

## Questions for the audit

**A. The headline: statement fidelity.**
1. Is `levinNPHard_L3COL : LevinNPHard L3COL R3COL` (`Hardness.lean:230`) the strengthened Step 2 of [PS10,
   Theorem 124.1] ("Cook's reduction can be applied to the witness y yielding a witness y′"; `pass-shelat-2010-ch4.raw.md`
   l. 646 ff.), with no hidden hypothesis? Check that `LevinReduction` (`NP.lean:134`) is used as defined, that the
   length regularity `|f x| = p(|x|)` holds for **every** `x` (including `x ∉ L` and malformed inputs) and that
   `N ≤ p(N)`.
2. Are `L3COL`/`R3COL` (`TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean:126`, `:130`) the language and
   relation of PS10's Graph 3-Colouring, and does the padded encoding (`padWord`, `padColWord`) stay inside them?
3. Do the two corollaries restate `NP.lean:689` and `:742` exactly, minus the hypothesis?
4. Against **[St73, Theorem, p. 22]** (attached; `p004-b001`) and **[AB09, §2.3]** (draft §2.3.6 item 2, `p066-b002`,
   the Levin notion): is the docstring's description (Karp form in [St73]; the deviation note: witness map, exact
   lengths, circuit route, the course variant of the gadget, the explicit witness colouring) accurate?

**B. Each step's reduction and efficiency (rule 15).**
1. **Step 1** (`Verifier`): the certificate `certOf` and `stripCert`, the verifier language in `P`, the tableau instance
   map `tabInst` and `exists_tabReduction`. Is the re-instantiation of `dagCktSatLang_NPHard`'s core
   (`TCSlib/Complexity/CircuitComplexity/CircuitSatNPHard.lean:93-127`) the disclosed specialization (overlap (a)), and
   is it [AB09, Lemma 6.10] = draft Lemma 6.31 (`p128-b003`, `p128-b004`)?
2. **Step 2** (`CircuitWitness`): `wireValues` and `R_3SAT_wireValues` against [AB09, Lemma 6.11] = draft Lemma 6.32
   (`p128-b005`, `p128-b006`) and Def 6.1 (`p118-b002`, `p118-b003`). Is `exists_R_3SAT_iff` (replacing the brief's
   `mem_SAT3_iff_exists_R_3SAT`) a justified, non-weakening change?
3. **Step 3** (`Gadget`, `UnaryArith`, `ColoringGraph`, `ColoringParse`): `colorInst` on `Fin N` with one gadget per
   clause code `c < (2K)³` (`N = 3 + 2K + 6(2K)³`), `K₄` for ill-formed or over-wide input, and the polynomial-time
   tests. Is the vertex count polynomial and the edge test correct?
4. **Step 4** (`ColoringWitness`): is `gadgetColor` proper whenever the assignment satisfies the formula, and is
   `colorWord` polynomial-time?
5. **Soundness** (`Soundness`): is the transport of `SATtoColorReduction` along the homomorphism
   `ReductionGraph (gadgetFormula K mem) →g gadgetSimpleGraph K mem` sound, with no second soundness proof?
6. **Padding and assembly** (`Padding`, `Hardness`): `B(n) = A(n+1)^a + n + 1` from `output_length_le`; is every map
   uniform `PolyTimeComputable` with no efficiency hypothesis? List any `Classical.choice` machine without its proof.

**C. The Bridge exception and Rule 10.**
1. **The bounds.** Does `Bridge.lean` hold **exactly** the 27 readers of the ruling (10 Complexity, `levinNPHard_iff`,
   16 course; S-1), each matching its owner's definition (the 17 `rfl`/`Iff.rfl`) or a correct case characterization
   (the 10 case lemmas)? Is each one used?
2. **The evidence.** Do the 43 coe-A errors fall on exactly the 20 definitional readers
   (`verification-r1.zip:seal/bridge-error-map.tsv`), and are the seven `simp [EdgeRelation]` readers exactly the
   scan's seven hits?
3. **Nothing else reads foreign definitions.** coe-A and seal B give 0 on the 11 other owners. Look for reads a seal
   cannot see: `show`/`change`/`decide` steps, `simp [X]`/`unfold X` of a foreign name outside the bridge, foreign
   matchers, and in particular **S-3**, the private `extract_run.match_1`. Is S-3 a Rule-10 violation, and at what
   severity? Is recording it for the Complexity owner enough?
4. **The paired controls** (50 pairs, ALL_OK): do they show that each new public definition has a working reader and
   that the seal detects a direct read?
5. **The quarantine.** `Bridge` is public and re-exported by the facades. Is the docstring's "the only place …" claim
   true, and is the exception bounded as DL-65 records it?

**D. The landing edits.**
1. **LE-h12-arith** (`le-arith.diff.txt`): are the three deletions complete (no remaining restatement), are the call
   sites correct, and is the `repeat' first` order (`apply divNum_poly | apply modNum_poly` before the arithmetic
   alternatives) what keeps `modNum` from being unfolded (`landing.md`)? decls2: 3 REMOVED, nothing else.
2. **LE-h12-strip** (`le-strip.diff.txt`, S-2): is the proof sound, minimal and through the equation lemmas? Does the
   N4 probe (`verification-r1.zip:n4/`) show what it claims, including the control? Grade S-2 and S-3.
3. **LE-h12-bridge** and **LE-h12-doc**: docstring-only (`checks/landing-edits-codeonly.txt`); do they say what
   EF-H12-R1 (A), F05(c) and F07 (a)–(c) require, and the [St73] final texts F1–F4, F6 of `ingest-report-st73.md`?
4. **LE-h12-priv** (S-6): is leaving `polyTimeComputable_colorInst_of` public acceptable?

**E. Duplication.**
1. **Report the searches you ran, with hit counts,** against TCSlib at the merge (`git grep <pattern> 11f33ef3 --
   TCSlib` and `56df3925` for the records side), Mathlib and Batteries, for each new public definition and lemma. At
   least: `R_3SAT`/`satAssignment`; `wireValues`/`DAGCircuit.values`, `CVAL`, `CVALPrefix`; `stripCert`;
   `padColWord`/`EncodingMachines.padTo` (and `ThreeColoring/Machines.lean:303`, `ComposeSecurity/Machines.lean:223`);
   `padGraph`; `clause_eval_eq_true_iff`/`cnf_eval_eq_true_iff` against core `Std.Sat.CNF`;
   `threeColorable_gadgetGraph_iff`/`threeColorable_ofSimpleGraph_iff`; `unaryDivConst_poly`/`unaryModConst_poly`;
   `polyTimeComputable_foldl_accept`/`polyTimeComputable_transduce`; `polyTimeComputable_syntaxOK`/`satSyntax_poly`.
2. **An undisclosed re-proof is a major.** After LE-h12-arith, does any restatement of a public row remain?
3. **The disclosed overlaps** (a)–(c), DL-64 (S-11), and overlap (b) (S-10): is each acceptable as disclosed, with its
   repayment scheduled? Is DL-65's "private" wording a records error to correct?

**F. Docstrings, sketches, attribution, size.**
1. Is every result tagged with a precise source location or marked as glue, with statement prose first, and is every
   nontrivial proof sketched (in particular `levinNPHard_L3COL`, `exists_tabReduction`, `R_3SAT_wireValues`,
   `polyTimeComputable_colorInst`, `properColoring_gadgetColor`, `polyTimeComputable_stripCert`)?
2. **[St73]** (attached): the citations "Theorem, p. 22; proof pp. 21–22; Fig. 1, p. 24" and the binding note; the
   `Gadget.lean:33-37` node map (course nodes `0…5` = St73's `v₁, v₂, v₄, v₅, v₃, v₆`, literals at `0, 1, 4`; the
   palette triangle instead of the arc `{t₁, t₂}`; the extra base edge of node `5`); `ColoringWitness.lean:30-31`
   ("the converse is similar", p. 21).
3. **[AB09]** (attached, draft): every [AB09] citation at the head (in-text and in `## References`; the ingest
   report checked 26 in-text citations and 13 parentheticals of the delivery, before LE-h12-doc), against the draft
   through the numbering map of `ingest-report.md`. CUP numbers that the draft cannot confirm are not findings by
   themselves (ruling in force 8); mismatched **content** is.
4. **S-5:** should the unused [AB09] entries of `Gadget` and `UnaryArith` go, and is `UnaryArith` correctly glue?
5. **[PS10]** tags against `pass-shelat-2010-ch4.raw.md` and the appendix (Definition 191.11).
6. Are the file sizes within policy (largest `ColoringParse`, 720 lines)?

**G. Evidence.**
1. **Grade `verification-r1.md` and its ZIP:** the merge and the binding argument (§1: identical `TCSlib` trees, so
   the landing's replay of `a3617cde` binds to the merge with the pin); the replay (27 modules, state check, S-4); the
   axiom census; the seals and controls; the scan; N4; decls2; lint; the PR at staging.
2. **Grade the review's and phase 2's evidence** (`review.md`, `phase2.md` and its ZIP) for what the landing did not
   re-run (the bridge necessity and owner-form demonstrations).
3. **Binding.** Does each piece of evidence bind to `11f33ef3`, or, for the merge, to `TCSlib` tree `05b0eecd`? A
   missing or non-binding piece of necessary evidence is a major.

**H. Source review: [AB09] ch. 2 and ch. 6** (attached `book.pdf`; you need only PDF pp. 55–80 and 117–130).
1. **Provenance:** the SHA-256 of the attached file against the `.md`/`.raw.md` headers; page range; "printed draft
   page = PDF page − 16".
2. **The raw files:** does each `<!-- pdf-page: N -->` section match the PDF's text layer for that page (sample at least
   pp. 56, 59, 61, 62, 65, 66, 118, 120, 121, 128)?
3. **The transcriptions:** for every block cited in the citation check or the numbering map (`p056-b002`, `p059-b004`,
   `p060-b002`, `p061-b001`–`b003`, `p062-b002`, `p065-b002`–`b004`, `p066-b001`, `p066-b002`, `p071-b003`, `p072-b001`,
   `p118-b002`, `p118-b003`, `p120-b002`–`b007`, `p121-b001`, `p121-b002`, `p128-b001`–`b006`): is the wording faithful,
   the number and printed page right, the confidence honest, and every condensation labelled? Are the flagged draft
   errors (Def 2.21, Thm 2.16's proof, Lemma 2.12's condition 3, Exercise 11, Exercise 6.11, Def 6.28) real?
4. **The numbering map** (`ingest-report.md` § *Numbering map*): is each draft number and page right? Can you confirm
   or refute any CUP number from your own knowledge (mark such statements UNVERIFIED-SOURCE unless you can quote CUP)?
5. **The citation check:** do its "match / partial / mismatch" verdicts hold, and do the post-LE-h12-doc docstrings fix
   the three mismatches?

**I. Source review: [GJS74] and [St73]** (attached `gjs74.pdf`, `st73.pdf`).
1. **Provenance:** SHA-256, page counts, printed-page offsets (+46, +18), and what each PDF does and does not print.
2. **GJS74:** the locator §II, p. 52 (`p006-b002`); Theorem 2.1, p. 53 (`p007-b003`) and its proof blocks; the appendix
   entry (`p016-b003`); the reference list (`p017-b001`, giving [St73]'s title); the Figure 1 description and its
   maintainer note (`p007-b007`); the "For k > 4" note.
3. **St73, page order (S-13):** do the four page-break continuities hold, and is the Theorem on printed p. 22?
4. **St73, transcriptions:** every transcribed block, in particular the Theorem (`p004-b001`), the proof of part 1)
   (`p004-b002`, `p004-b003`, `p003-b001`), the $k$-colourability remark (`p003-b002`), the cross-over definitions
   (`p003-b003`, `p002-b001`, `p002-b002`).
5. **St73, figures:** Figure 1 (`p006-b002`) against the page image (the gadget $G^*$ and properties i), ii)); the
   **low-confidence** Figure 2 (`p006-b003`: the edge list of $G_C$, 19 nodes, 34 arcs) and Figure 4 (`p007-b002`);
   Figure 3 (`p007-b001`). Where the drawing cannot be read with certainty, say what is uncertain.
6. **The gadget comparison** (`ingest-report-st73.md` § *Gadget comparison*): is the course gadget Stockmeyer's Fig. 1
   gadget node for node, and are the two differences (palette triangle; node-5 edges) stated correctly?
7. **`sources.json`:** are the `GJS74` and `St73` entries right, and the AB09 `documents` list?

**J. Anything undisclosed.** S-1 to S-13 are the known items.

## Deliverable

`findings-r1.md`, in this form:
- **Findings** `G57-01`, `G57-02`, …, each with: severity (blocker / major / minor / note), part (PR #398 or the ingest
  pair), file and declaration or anchor, claim, evidence (quoted lines, page and anchor, commands), and proposed fix.
- **A table grading S-1 to S-13** (for each: agree / disagree, severity, and whether it blocks).
- **A table per ingest pair:** blocks checked, blocks with corrections, the verdict **PASS**, **PASS WITH CORRECTIONS**
  (list them) or **FAIL**, and the confidence of the two low-confidence St73 figure blocks after your check.
- **The searches you ran,** with hit counts.
- **The audited head,** the records pin, the verification ZIP's SHA-256 as you computed it, and the SHA-256 of each
  attached PDF as you computed it.
- **Counts by severity.**
- **A verdict for PR #398:** CLEAR (zero blockers and zero majors) or HOLD.

Return it as Markdown in the chat, or as a ZIP with `findings-r1.md` at its root if you have search logs or scripts.
