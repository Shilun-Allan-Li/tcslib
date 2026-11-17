# Gate 45 · resolutions, round 1 · HOLD → landing edits LE-g45 and LE-g45b

Codex's verdict is **HOLD overall: #358 CLEAR, #359 HOLD**: 0 blockers, 1 major (G45-01, #359), 1 minor (G45-03,
#359), 1 note (G45-02, #358).
- **Findings:** `findings-r1.md` (verbatim, filed by the maintainer; the `audit/target-review.tsv` it cites was not
  received).
- **Audited:** #358 at `a616adcac0760ab56b1b0a2a4869f4763843f9ab` (merge base `e1d39836`); #359 at
  `73aedcdaaaffef7e69ab012d9b9195f150bae68d` (stacked on `a616adca`); records `8c5875fa268a622e4e166da5f7a992715097c2c7`;
  exchange `059331913c8a5380d3ae53e5e9dffa3c7ff6e2b4`.
- **Ruling (Seyoon), decision log "Gate 45 round 1 (Codex)":** fix now in #359 by a landing edit. Move
  `eval_node_nil` unchanged (same full name) from `Hierarchy.lean` into `Combinators.lean`, make `const_eval` a proved
  citation (admissions 98 → 97), and fix the G45-02/03 wording; then re-replay and run round 2.

Codex found **no mathematical gap**. Its round-1 confirmations, which round 2 does not reopen:
- **Targets.** All **98** admitted targets are sound as stated, with non-vacuous hypotheses, and strong enough for the
  named r3 consumers (C1–C25, N1–N13, F1–F3, F5–F10; the per-group table sums to 98). C16's `σ 0` reading is harmless and
  disclosed. No definition has a `sorry` body; `sorryAx` reaches exactly two definitions and three theorems
  (`toNANDForm`, `toNANDForm_eq`, `layerNAND`, `layerNAND_gates`, `layerNAND_output`) through N2 and N12–N13 only, which is
  acceptable for the statement phase.
- **#358 (O1).** The move is exactly as stated (4 files, +279/−184); all seven public declarations are sound; the five
  repairs are semantics-free; the frozen `TreeNCAC` surface is unchanged, and its 2 seal failures and 4 foreign unfolds
  are pre-existing (G6A-F05).
- **Reuse.** LE-ren completely removes the `rename` family; no other duplicate of the `reidx`, `widenCircuit` or
  `restrictCircuit` families remains. G45-01 is the only additional exact overlap.
- **Sources.** 112/112 anchors resolve; 18 exact and 6 rendering-different quotations check.
- **Evidence.** 13/13 outer checksums, 483/483 verification-archive files, 42/42 source copies, 86/86 bundle sections;
  six worker commits reproduce hash-for-hash; declaration drift 267/0/0. Snapshot-#5 replays R1 9/9 (state 1429) and R2
  20/20 (state 1440); admissions +0 / +98 exact; axiom census 544 constants with `sorryAx` in the 98 targets and five
  dependents.
- **Carry-forward: confirmed** for the claimed checks (strict A/B and coe-B seals and the controls stand on equal
  closure keys and identical coe-A records; all 20 canonical owner records and 26 reused tools match).
- **Per-variant counts** (strict A / strict B / coe-A / coe-B): owners **7717 / 7718 / 7717 / 7718**, 2 errors per
  variant (`TreeNCAC`, pre-existing); O1's owners 4221 per variant; delivered roots 13762/13763/13761/13762, all clean;
  root coe-A on #5 14,074 requests, 0 errors. A/B differ by `PolyExpr.eval`; strict/coe differ by the projection
  `CoeFun` instance, absent from `ComputationalModels`' closure.
- **Grades.** G6A-F01–F15 all agreed (F01 limited to the `rename` duplicate, with G45-01 the further overlap; F07 is
  G45-02).

| Finding | Grade | Resolution | Evidence and pointer |
|---|---|---|---|
| G45-01 | **major** (#359) | **Fixed by LE-g45**, commit `ad9c4fc701ed145cbc96acceefaad447398c8321` on `73aedcda` (tree `c3608d46…`), signed by the records key. `BoolCircuit.eval_node_nil` is **moved** from `CircuitComplexity/Hierarchy.lean` (old `:104–108`) into `FormulaArith/Combinators.lean` (`:412` at `ad9c4fc7`, `:415` at `d154c883`), inside `namespace BoolCircuit` just before `TreeCircuit.const`, with the same full name, binders, statement and docstring. **Disclosed deviation:** its proof changes from `cases b <;> simp [TreeCircuit.eval]` (an explicit unfold of `Basic`'s `TreeCircuit.eval`) to `cases b <;> simp [TreeCircuit.eval_node_true, TreeCircuit.eval_node_false]`, `TreeDAG`'s public readers (Rule 10). `Hierarchy`'s two users (`:146` `restrictCircuit_eval`, `:192` `Language.zero_inTreeSize`) resolve through `Hierarchy → TreeNCAC → Combinators`; there is no import cycle. `TreeCircuit.const_eval`'s statement is byte-identical and its proof is now `rw [TreeCircuit.const_eq]; exact eval_node_nil b x`, so it leaves the admitted-target inventory: **admissions 98 → 97**, exact. The lemma is an [AB09]-chapter (`Hierarchy`) lemma now homed in the GSW-side `Combinators`; round 2 asks whether that home is acceptable. | `le-g45.md` §"The edit", §"Checks" (admissions, decls2 move-only, axioms, coe-A, unfold scan); `le-g45.diff.txt` (`c8edd59a…`); `le-g45-evidence.zip` (`983e4238…`). |
| G45-02 | **note** (#358, inherited by #359) | **Fixed by LE-g45** (prose only, on #359; #358 unchanged). `Combinators.lean:16–18` now reads "promoted with its computation unchanged; its proofs carry the five Q2-approved Rule 10 repairs." #358 keeps the old sentence at `a616adca`; the stacked #359 replaces it, so the merged result carries the new wording. | `le-g45.md` §"The edit"; `le-g45.diff.txt`. |
| G45-03 | **minor** (#359) | **Fixed by LE-g45** at `Barrington.lean:43` (Orders convention) and `:339` (C9 docstring): `(13254)` is called Bar89's **one-based** cycle notation, whose zero-based form `(0 2 1 4 3)` is what the code implements. **Completed by LE-g45b**, commit `d154c8830fc8ffc52671b41992e7dbef61e30959` on `ad9c4fc7` (tree `be58919e…`), for the remaining loose phrasings: `:23` (module docstring, `(12345)`/`(13542)`), `:110` (`sigma1`) and `:119` (`sigma2`) now name Bar89's one-based notation and give the implemented zero-based forms `(0 1 2 3 4)`/`(0 2 4 3 1)` (line numbers at `d154c883`). C16's "1-based state" (BV14's state indexing, `:459`) is accurate and unchanged. Formal permutations and statements are unchanged (comment-strip identity below). | `le-g45.md`; `le-g45b.md` §"The edit", §"Code identity"; `le-g45b.diff.txt` (`68f62328…`); `le-g45b-evidence.zip` (`9f41e81b…`). |

**LE-g45b also** updates `Combinators`' `## Main results`: `const_eval` gets its own entry ("proved from
`BoolCircuit.eval_node_nil` …, which moved here from `Hierarchy.lean`") and leaves the "(F3; targets)" entry, which is now
exactly the 17 remaining F3 targets. LE-g45b is comments and docstrings only: the comment-stripped code of both files is
byte-identical to `ad9c4fc7`, with 3 mutation controls per file caught and 1 negative control equal.

**Checks at the new head `d154c883`** (detail in `le-g45.md` and `le-g45b.md`):
- **Replay.** LE-g45 rebuilt the 16 downstream modules on a `cp -al` copy of `olean-replay-6a-stmt`
  (→ `olean-replay-6a-stmt-g45`), and LE-g45b the same 16 on a copy of that (→ `olean-replay-6a-stmt-g45b`): each 16/16 rc
  0, 0 errors, only `sorry` warnings (68, in the 7 rebuilt target modules; the other 29 targets are in the 4 reused
  modules `Defs`, `Eval`, `NANDForm`, `NANDLayering`); state **1440/1440 OK** at each head; rebuilt
  oleans link count 1; snapshot #5 and the parent trees rehash 0/0/0. Output maps 1471 entries, `3cb140cb…` (LE-g45) and
  `fa206774…` (LE-g45b).
- **Admissions 97**, exact (row map minus `rename_eval`, `depth_rename`, `const_eval`); against the #5 re-replay the
  admitted set differs only by `const_eval`. LE-g45b's admitted set equals LE-g45's.
- **decls2:** one REMOVED (`Hierarchy.lean:105`) and one ADDED (`Combinators.lean:412`) row for `eval_node_nil` with
  identical normalized statements: a move. Nothing else.
- **Axioms:** 545 constants; `sorryAx` in 102 (97 targets + the same 5 dependents); `eval_node_nil`, `const_eval` and
  Hierarchy's two users use `[propext, Classical.choice, Quot.sound]`. LE-g45b's probe logs are byte-identical to LE-g45's.
- **Rule 10 (canonical coe-A).** LE-g45, base `73aedcda` against head: `Combinators` 174/0, `Barrington` 119/0,
  `Hierarchy` 355 requests with 2 errors at both; request sets equal. LE-g45b, head against LE-g45's head: `Combinators`
  174/0, `Barrington` 119/0, equal. Explicit-unfold scan: 0 new foreign unfolds; one removed (the old
  `simp [TreeCircuit.eval]`).
- **Lint:** `campaign_style_lint --check8b` 25 FAIL / 390 WARN, FAIL/WARN line sets identical at base and each head; only
  INFO line counts change. `style_lint` 2 findings, pre-existing `Hierarchy:17` false positives.

**Disclosed pre-existing item (not a round-1 finding).** `Hierarchy`'s canonical coe-A seal fails twice, in
`Language.InTreeSize.inSIZE` ("Invalid `⟨...⟩` notation", "No goals"), with **equal** errors and request sets at
`73aedcda` and at `ad9c4fc7`. `Hierarchy` was unchanged by the series before LE-g45 and phase 2 did not seal it, so round 1
did not see it. It is not introduced by LE-g45; it is a Rule 10 item for the clean-up track, like G6A-F05.

**Known records/PR slips (disclosed, not fixed here):** #359's **title** still says "(98 targets)" (its body says 97);
#359's description names `olean-replay-6a-stmt-g45b` as the adoptable replay, but that tree is built on snapshot #5, and
snapshot #6 has since been adopted at `8060f6b7` (the #357 merge), so #358 and #359 re-replay on #6 before merge (a merge
condition, not an audit item).

Then Gate 45 round 2 (Codex) at #359 `d154c883`, with #358 unchanged at `a616adca`.
