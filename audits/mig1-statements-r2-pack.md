# External audit pack — MIG-1, round 2: the statement gate's repairs and re-measurement

Round 2 of the MIG-1 statement gate. Round 1 (`audits/mig1-statements-findings.md`, attached
verbatim): **gate open, 0 blockers, 1 major, 3 minors**, no false public spec and no changed
machine transition. The round-1 pack and bundle are immutable and unchanged; this pack
supplements them. The gate closes on a round with **zero blockers and zero majors**. Record
findings in `audits/mig1-statements-r2-findings.md`.

**Campaign context.** The machine-library migration (`machine-library-design.md` §2, §16;
backlog MIG-1 with MIG-9, MIG-11, MIG-17, MIG-20), under the Arora-Barak chapters 3-4 plan.
MIG-1 gives every existential machine row of eight library files a named public witness with
spec theorems, makes each row a short corollary with its statement unchanged, deletes Catalog's
304 private `f2_` copies (with 45 `a2_` and 7 `catalog_redirect*` declarations), and retires the
six R3 canonical `_run` rows. Round 1's pack describes the unit, the probes and the plan; this
pack describes only what changed and what was re-measured.

**What did not change** (MEASURED). The unit `MIG1Statements.lean.txt` (2,950 lines), the
spec-probe tail, the bridge probe and the axiom-probe print list: the round-2 runner rebuilds
them from the round-1 templates at the tip and they are **byte-identical** to the round-1
artifacts. So are the 26 witnesses, the 45 statements, the 55 corollaries, the identity
manifest, the rename map and the moved-name map. None of the ten MIG-1 files changed since
round 1 (the same git blobs; provenance log).

**What changed underneath** (MEASURED, provenance log). The campaign moved from `1781a230`
(round 1) to the tip `99ad2f98` (`99ad2f9894121f45c79a27722d9466223be16473`):
- PRs #85 (RD-2, the formula kit) and #86 (stage 2, the RAM simulation) added 8 modules (632
  now); 6 of them import a MIG-1 file;
- the MIG-0b round-2 gate closed (`6b5345cb`; 0 blockers, 0 majors, 3 minors), so
  MIG-0b's landing set is final.

**Every round-2 check was run at `99ad2f98`**, read-only, against its olean snapshot `oleans-t1`,
Lean `v4.25.0`. In this pack `r2/` is `audits/evidence/mig1/gate/r2/`, and "the X log" is
`audits/logs/mig1-statements-r2-X.log`.

**Maintainer note (since the measurement; MEASURED at `dc891632`).** Two merges followed the
round-2 measurement:
- **H2-M** (PR #88) moved the step block out of `CodeSimulator.lean`, one of the ten MIG-1
  files. The R3 site `copyTM_run` (round 1: `:1295`) is now at `:1282`; CodeSimulator's staying
  declarations are freeze-checked unchanged, and nothing else measured here is in that file.
- **Hydroxyi's ARM merge** (`8c23f3bc`, pushed to the campaign branch) touches none of the ten
  files. It adds two code citations of `Turing.FinTM.computesFunInTime_lengthBits`
  (`ClassPSPACE/TQBFHardVerifier.lean:247, 264`), whose statement MIG-1 keeps. The import
  graph grows to 706 modules, 282 of them in the ten files' downstream closure (with the ten).

MIG-1 S re-measures consumers, closures and line positions at its own landing base, as round 1
requires. MIG-0b's landing follows C1's (#87) and precedes MIG-1 S, so the head bound will be
MIG-0b's interval lemma in `Finite` (decision 3).

## Resolutions

1. **Finding 1 (major): the extended contract's preparation step was retargeted at a weaker
   lemma. Repaired** as the auditor preferred. Loop's private `loopHost_prepare` is
   strengthened in place, for both `forward` modes, with the fuel-head clause, and its two
   callers are adjusted. Catalog's extended contract replaces Loop's `loopHost_contracts` over
   surviving home lemmas only. **Demonstrated by elaboration** of
   `r2/overlay/LoopOverlay.lean.txt` (overlay log): exit 0, 0 errors, 0 sorries, every key
   declaration free of `sorryAx`. The fate is corrected.
2. **Finding 1, generalized.** The systematic retarget table `r2/data/retarget-table.tsv`
   covers 59 moving or absorbed declarations and their 215 region citations. It finds **no
   WEAKER or inaccessible case besides `loopHost_prepare`**. Lean checks (`r2/checks/`) restate
   every non-verbatim Loop-sourced copy and prove it from its retarget. Their negative control
   at the tip fails exactly at `loopHost_prepare` and at the contract replacement that round 1
   already planned (retarget log).
3. **Finding 2 (minor): the runner did not propagate failures; the builder accepted an empty
   template set. Repaired.** `r2/scripts/runall.sh` is rewritten: `set -euo pipefail`,
   statuses accumulated, every count compared with `expected-r2.json`, an exact identity
   control, an input precheck. `r2/scripts/build_unit.py` refuses bad template sets and writes
   atomically. Three negative controls (runner-negative-control log).
4. **Finding 3 (minor): the bundle lacked files its reproduction description names.
   Repaired.** `r2/BUNDLE-FILES.txt` lists the manifests, the templates,
   `campaign_style_lint.py`, `consumer-names.json`, the overlay, the checks and every log.
   `r2/EVIDENCE-MAP.tsv` maps each runner input to its repository file; the 36 round-1 inputs
   are checked byte for byte. The runner exits 2 before writing anything if an input is missing.
5. **Finding 4 (minor): three descriptions overstated their evidence.** The corrected
   sentences are below ("Corrected descriptions").

## Finding 1: the repair

**The strengthened lemma** (private, `Build/Loop.lean:1241`; overlay part 1). Its conclusion
gains one conjunct; the hypotheses and the `forward` parameter are unchanged:

```lean
    ∃ (c : Cfg F.k Bool F.State x) (t : ℕ),
      c.state = none ∧ c.output = Nat.bits (R x.length) ∧ t ≤ 5 * T x.length + 7 ∧
      (loopHostM body F anchor forward findMode).tm.runFrom
        ((loopHostM body F anchor forward findMode).tm.initCfg x) t = loopReady body F c ∧
      ∀ i, -(T x.length : ℤ) ≤ c.workTapePos i ∧ c.workTapePos i ≤ T x.length
```

The body is kept. The new branch is proved for the actual fuel endpoint
`c = F.tm.runFrom (F.tm.initCfg x) u`. Here `u ≤ T |x|` is the first halting time from
`loop_first_halt`. The interval lemma at the initial configuration, whose heads are at 0, gives
`-u ≤ c.workTapePos i ≤ u`. This is Catalog's own argument (`:7350–7354`), retargeted:

```lean
  · intro i
    have h := Finset.mem_Icc.mp
      (mig0bStandIn_workTapePos_runFrom_mem_Icc F.tm (F.tm.initCfg x) u i)
    have hh : -(u : ℤ) ≤ c.workTapePos i ∧ c.workTapePos i ≤ u := by
      simpa [c, MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords] using h
    omega
```

**The callers.** `Loop.lean:2116` lies inside the replaced contract, whose moved text
destructures the clause as `hfuel` (Catalog's own line). `Loop.lean:4805`, in
`exists_emitLoopTM`, discards it with one token: `⟨…, hprepare, -⟩`.

**The overlay** (`r2/overlay/LoopOverlay.lean.txt`, 5,743 lines). `r2/scripts/build_overlay.py`
builds it from the tip's files by asserted replacements only.
- **Part 1** (5,180 lines) is the tip's `Build/Loop.lean` verbatim with:
  - (a) the strengthened `loopHost_prepare` and the caller edits;
  - (b) a labelled stand-in, `private mig0bStandIn_workTapePos_runFrom_mem_Icc`. It is
    MIG-0b's `Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc` (landing `Finite.lean:386–408`);
    only the name, the visibility, the namespace and the docstring differ
    (`standin-vs-mig0b.diff`). At landing it is dropped and each citation names the MIG-0b
    lemma. `workTapePos_step_le` and `runFrom_succ_eq_step'` are at the tip, so no further
    stand-in is needed;
  - (c) the moved loop-budget family `loopCall_heads`, `segment_heads`, `space_radius` and
    `seamed_space`: Catalog's text with `f2_` dropped, the head bound read through
    `Finset.mem_Icc.mp`, and a proof sketch added to each docstring;
  - (d) Catalog's extended `f2_loopHost_contracts`, moved over Loop's `loopHost_contracts`.
    Loop's docstring is kept and gains a paragraph on the extension. The statement and proof
    are Catalog's under these retargets:
    - `f2_loopHost body F anchor findMode ↦ loopHost body F anchor findMode`, Loop's
      abbreviation of `loopHostM body F anchor false findMode` (round-1 bridge probe: `rfl`);
    - `f2_loopHost_prepare … ↦ loopHost_prepare … false …`, and the same for `_start`;
    - every other `f2_X ↦ X`; `f2_head_steps` ↦ the stand-in through `Finset.mem_Icc.mp`;
    - the coefficient made explicit (below).

    No `f2_` or `a2_` token remains anywhere in the overlay (asserted by the builder).
- **Part 2** (525 lines) is the unit's Loop part (unit lines 799–1488):
  - its three gate-shim blocks are dropped (the overlay has the originals);
  - two docstrings no longer name `f2_` declarations (`part2-vs-unit.diff`);
  - **every `sorry` is replaced by a proof** over the declarations of part 1:
    - `loopHostTM_contracts`: the moved `loopHost_contracts`, its two head clauses dropped;
    - `loopHostTM_decides`, `loopHostTM_finds`: the bodies of `exists_loopTM` and
      `exists_loopFindTM` over the named host, with `c = 10`;
    - `loopHostTM_spaceUsed_le_budget`: the moved contract and `seamed_space` (the spec
      probe's glue, now relative to the real declarations);
    - `emitLoopTM_computes`: the tip's `exists_emitLoopTM` body, extracted, the host named;
    - `callTM_run`: `emCall_first`.

The overlay imports exactly `Loop.lean`'s six imports and `TuringMachine.Simulation` (the unit
Loop part's one extra `@imports`, already in Loop's closure). It does not import `Loop`. Being a
full copy of `Loop`, it is elaborated in Loop's import closure: the cut-check method.

**The explicit coefficient (a private statement change).** Catalog's contract states
`∃ c : ℕ, ∀ x, …` and opens its proof with `refine ⟨f2_loopHost_bound, ?_⟩`. The public
`loopHostTM_contracts` names `10`, which an `∃ c` statement cannot supply. So the moved
contract takes the transform that round 1's manifest applies to `loopHostTM_contracts` and to
its probe shim `loopHost_contracts_heads`: `∃ c` removed, `c ↦ 10`, the `refine` line deleted.
`loopHost_bound` reduces to `10`; the proof's internal bounds still use it.

**Result** (MEASURED; overlay log, elaboration log §11):
- **Elaboration**: exit 0, 0 errors, 0 `declaration uses 'sorry'` warnings. The 61 other
  warnings are exactly the multiset (message and argument) that the tip's `Loop.lean` gives
  alone: no warning is new.
- **Axioms**: 23 `#print axioms` lines, every one within `{propext, Classical.choice,
  Quot.sound}`. They cover the stand-in, `loopHost_prepare`, `loopCall_heads`,
  `loopHost_contracts`, `segment_heads`, `space_radius`, `seamed_space`, the four loop rows,
  the six Loop-part specs (`loopHostTM_contracts`, `_decides`, `_finds`, `_spaceUsed_le_budget`,
  `emitLoopTM_computes`, `callTM_run`) and the six `MIG1Gate.row_*`.
- **No sorry remains** in the overlay, so no remaining sorry warning needs naming.
- **Diff** of part 1 against the tip (`part1-vs-tip.diff`): 12 hunks, +219/−19 lines. Every
  added line has at most 100 columns. The 63 over-width lines of part 1 are verbatim tip lines;
  the tip has 65, and the 2 that the moved contract replaced are wrapped.

| Tip line | Hunk content | +/− |
|---|---|---|
| 9 | `import …Simulation` | +1/0 |
| 1232 | stand-in (25 lines, not landed); `loopHost_prepare` docstring, statement | +34/−3 |
| 1269 | `loopHost_prepare` proof: `?_, ?_, ?_` and the clause | +7/−1 |
| 2037 | `loopCall_heads` (moved) | +29/0 |
| 2059 | contract docstring: the extension paragraph | +10/−1 |
| 2094–2209 | contract statement and proof (moved); the three space lemmas (moved) | +130/−9 |
| 2282 | `exists_loopCfgTM` body: `c = 10`, head clauses discarded | +4/−2 |
| 2519 | `exists_loopFindTM` body: the same | +3/−2 |
| 4801 | `exists_emitLoopTM` body: `, -` | +1/−1 |

**Private statement changes in Loop** (`overlaycheck.py stmts`, which cuts at the proof's `:=`
and skips a `let`/`have` binder). Exactly two:
- `loopHost_prepare` (the clause);
- `loopHost_contracts` (the planned replacement: explicit `10`, two head clauses).

Added private declarations: the stand-in (not landed) and the four moved lemmas. Body-only
changes: the three public rows above, statements unchanged. At F-C their bodies are replaced by
the `MIG1Gate.row_*` proofs anyway, which subsumes these edits. Nothing else changes. (The
campaign's `tools/privstmt.py` cuts at the first `:=` and stops inside `(input := x)`; it
reports only `loopHost_prepare`. Round 2 therefore uses the depth-aware cut.)

## Finding 1 generalized: the retarget table

**Population** (MEASURED, `r2/scripts/retarget.py`; retarget log). Every region declaration
whose fate moves it into a home (47) or absorbs it into a gated statement (12), and every region
name its code cites, statement and proof: **215 citations**. For each citation the table
records:
- the cited name's round-2 fate and its retarget;
- where the retarget lives and whether it is private;
- a statement comparison (comment-stripped, whitespace-normalized, cut at the proof's `:=`,
  with the prefix map and the moved-name map applied to the copy);
- accessibility. A private retarget must live in the receiving home; a public one must be in
  the home's import closure (from the `import` lines of the tree and of Mathlib).

| Class | Citations |
|---|---|
| IDENTICAL (copy of a same-home original; a public duplicate the bridge probe proves) | 53 |
| MOVES-WITH (moves to the same home: the same text, renamed) | 112 |
| GENERALIZATION (listed below) | 11 |
| **WEAKER at the tip** (`f2_loopHost_prepare`; after the repair, `forward := false`) | **1** |
| NOT-CARRIED (cited by an absorbed declaration whose proof is replaced, not moved) | 38 |
| PROBLEM or DIFFERS | 0 |

- The 38 not-carried citations come from 7 absorbed declarations: `f2_counter_computes`,
  `f2_unary_sharp`, `f2_strip_linear`, `f2_cond_time`, and `f2_splitSolve_of_body`, `_source`,
  `_closed`.
- The 11 generalizations:
  - `f2_head_steps` → MIG-0b's interval lemma by `Finset.mem_Icc.mp`, 6 citations, from
    `f2_poly_space`, `f2_counter_count_space`, `f2_counter_heads`, `f2_segment_heads`,
    `f2_seamed_space` and the contract; `Finite` is in every home's closure;
  - `f2_loopHost` → `loopHost`, 2 citations (`rfl`);
  - `f2_loopHost_start` → `loopHost_start` (`forward := false`);
  - `f2_loopHost_contracts` → the moved contract (`⟨10, ·⟩`);
  - `f2_catalogPair_inverse` → `Turing.eq_pairEncode_of_pairDecode`, binders reordered
    (bridge probe).
- **Accessibility.** 174 citations are accessible now. 3 are accessible after F-A's
  `import Mathlib.Algebra.BigOperators.Fin` in Simulation (decision 4): `Fin.sum_univ_add` for
  `f2_branch_space`, `f2_cond_space` and `a2_map_space`. 38 are not carried. **None is
  inaccessible.** Every copy cited by a moving declaration has its original in the same
  receiving home, so no private retarget crosses files.

**Lean checks** (`r2/checks/`; retarget log). Twenty Catalog copies are sourced in Loop with
code not identical to the original: 14 that instantiate at `forward := false` (one of them,
`f2_loopHost_prepare`, only after the repair), `f2_loopHost_anchor_return` (with
`pre := []`), 4 statement-identical copies and the contract. For each, the copy's
statement is restated (comment-stripped, `private lemma f2_X ↦ example`) and proved in one step:
`apply X (forward := false) <;> assumption`, or `⟨10, loopHost_contracts …⟩`. A 21st example
restates `f2_head_steps` from the stand-in.
- `RetargetChecks-r2`, after overlay part 1: **21 examples, 0 errors**.
- `RetargetChecks-tip`, the negative control after the tip's `Loop.lean`: **exactly 2 errors**.
  They are in the examples restating `f2_loopHost_prepare` (the missing clause, finding 1) and
  `f2_loopHost_contracts` (the two head clauses: the replacement round 1 already planned).

These checks cover all modified copies, not only the cited ones: **no other copy is stronger
than its original.** Round 1's statement-identity verdicts are also unchanged under the
depth-aware cut. Round 1's `region.statement` cut 3 of the 264 copies with a source early, and
no verdict changes.

## The user's decisions (binding, 2026-10-14)

The five open questions of round 1 are decided, all as recommended.

1. **The decision-loop S-form space family is dropped.** The 14 `a2_` ledger lemmas (433
   lines) are deleted; `exists_loopTM_spaceUsed` is a corollary of
   `loopHostTM_spaceUsed_le_budget`.
2. **The eight citation specs are proved at S.** The records distinguish "proof supplied" from
   "sorry-free". MEASURED (s-records log) by a text scan of the unit and the spec-probe tail
   that walks through proved unit theorems; not a kernel check.

   | Spec (proof supplied at S) | Sorry-free from | Because of |
   |---|---|---|
   | `callTM_run`, `redirectTM_runFrom` | S | — |
   | `polyUnaryTM_computes`, `pairLenCheckTM_computes` | S | — |
   | `stripLastTM_computes` | F-A | `timedCondTM_computes` |
   | `splitSolveTM_computes` | F-C | `loopHostTM_finds`, `lengthBitsTM_computes` |
   | `splitSolveWithTM_computes` | F-C | `loopHostTM_finds`, `lengthBitsTM_computes` |
   | `splitSolveTM_spaceUsed` | F-C | the budget, `lengthBitsTM_computes` |

   The overlay shows the Loop specs that the split specs need are provable in Loop's closure.
   They still land at F-C, and stay sorried at S.
3. **The single run head bound is MIG-0b's `MultiTapeTM.workTapePos_runFrom_mem_Icc` in
   `Finite`.** MIG-0b lands before MIG-1 S, and MIG-1 adds no head lemma of its own. Its moved
   proofs cite the interval form through `Finset.mem_Icc.mp`, as the overlay does through the
   stand-in. H2's `abs_workTapePos_runFrom_sub_le` stays as H2's same-name corollary beside it.
   Consequences:
   - the unit's Part 1 statement of that lemma, kept here for the identity counts, is **not in
     MIG-1's landing set**: MIG-1 lands 70 public names, not 71;
   - `f2_head_steps`'s fate becomes "duplicates an existing public declaration" (below).
4. **`Mathlib.Algebra.BigOperators.Fin` is imported in Simulation** at F-A, so
   `Fin.sum_univ_add` replaces `f2_sum_add` and `a2_map_sum`.
5. **`ComputesInTime.spaceUsed_le` is homed in Simulation.**

## The corrected deletion plan (round 2)

`r2/data/deletion-plan.tsv` (378 rows; deletion-plan log). Round 1's classifier, re-run at the
tip, reproduces round 1's table byte for byte. The round-2 classifier (`region_r2.py` with
`fates_r2.json`) differs in **exactly two rows**: `f2_loopHost_prepare` (finding 1) and
`f2_head_steps` (decision 3). All counts MEASURED; lines include docstrings.

| Fate | Decls | Lines |
|---|---|---|
| Delete: `f2_` copy code-identical to its home source | 232 | 4,351 |
| Delete: `catalog_redirect*` copies of Wrappers' redirect family | 7 | 77 |
| Delete: statement-identical copy, different proof (a) | 5 | 314 |
| Delete: modified copy, re-targeted at the original (d) | **15** | 564 |
| **Delete: `f2_loopHost_prepare`; its clause is added to Loop's original (F-C)** | **1** | **50** |
| Delete: duplicates a public declaration (round 1's seven **and `f2_head_steps`**) | **8** | 124 |
| Delete: dead | 12 | 213 |
| Delete: used only by deleted declarations | 5 | 142 |
| Delete: reached only from the decision-loop S-form (the `a2_` ledger; decision 1) | 14 | 433 |
| Absorbed into a gated statement (round 1's thirteen less `f2_head_steps`) | **12** | **499** |
| Move, renamed: forwarding map → Primitives | 28 | 721 |
| Move: polynomial space → Primitives | 4 | 196 |
| Move: counter space → TimeConstructible | 2 | 97 |
| Move: conditional ledger → Wrappers | 5 | 109 |
| Move: loop budget → Loop (b) | 4 | 101 |
| Move, replacing the original: the extended `loopHost_contracts` (c) | 1 | 178 |
| Move: pair length → Primitives | 1 | 11 |
| Public: space rows, corollaries in place | 20 | 922 |
| Public: `rewind_scan_heads`, `rewind_heads` moved to Simulation | 2 | 70 |
| **Total** | **378** | **9,172** |

(a) `f2_loopHost_halt_return`, `f2_loopCall_frame`, `f2_loopHost_accept`, `f2_loopHost_round`,
`f2_splitBody_round`. (b) `loopCall_heads`, `segment_heads`, `space_radius`, `seamed_space`.
(c) With the explicit `10` and the seam and terminal head clauses. (d) `f2_loopHost` and
**14** old-host phase lemmas (round 1: 15).

**F-C, revised** (Loop; replay **97** modules, MEASURED at the tip; round 1: 91 at `1781a230`):
1. **strengthen `loopHost_prepare`** with the fuel-head clause (+16/−4 lines in the overlay,
   MEASURED);
2. the extended contract replaces `loopHost_contracts`, with the explicit coefficient;
3. move `loopCall_heads`, `segment_heads`, `space_radius` and `seamed_space`; the head-bound
   citations name `MultiTapeTM.workTapePos_runFrom_mem_Icc` through `Finset.mem_Icc.mp`;
4. prove the five Loop specs (`loopHostTM_contracts`, `_decides`, `_finds`,
   `_spaceUsed_le_budget`, `emitLoopTM_computes`) as in the overlay;
5. swap the six rows to their `MIG1Gate.row_*` proofs. The overlay's three row-body edits
   disappear with the swap: `exists_emitLoopTM`'s body, with its `, -`, becomes
   `emitLoopTM_computes`'s proof.

The other batches are as in round 1, with the replay closures re-measured: S and F-A **212**,
F-B **82**, F-D **34**. S introduces no head lemma (decision 3). The size estimate stays about
**−7.0k** (ESTIMATE): the repair adds about 20 lines, and decision 3 removes the 25-line
absolute-value lemma from MIG-1's share.

## Re-measurement at the tip (one runner pass; all MEASURED)

`r2/scripts/runall.sh` at `99ad2f98` with `oleans-t1`: **exit 0, `RESULT: PASS`**, 133 s. Every
check equals `r2/scripts/expected-r2.json`, whose values are round 1's except where noted. The
runner's first pass at the tip, with all round-1 values, deviated only in the two replay values
below and in the name screen. The screen failed because the rewrite had dropped the step that
writes its input `work/part-lines.json`; the step is restored.

Unchanged from round 1:
- **Unit** (2,950 lines): exit 0, 0 errors, 31 sorry and 6 other warnings. **Spec probe**: 0
  errors, 70 sorry, 6 other. **Bridge probe**: 0 errors, 0 warnings.
- **Eight cut checks**: 0 errors each. Sorry warnings: Simulation 1, Composition 4, Wrappers 7,
  Encoding 2, TimeConstructible 4, Loop 13, Primitives 31, Catalog 31. Import union exact.
- **Rebuild**: the unit, the spec-probe tail, the bridge probe and the axiom print list are
  byte-identical to the round-1 artifacts.
- **Identity**: 158 entries, 0 failures. The mutation control exits 3, with exactly
  `timedCondTM`, `loopHostM` and `prependTM_computes`.
- **Axioms** (130 publics): 46 sorry-free, 84 with `sorryAx`, none nonstandard.
- **Names**, against the tip's 14,300 declarations in 575 modules (round 1: 14,137 in 569): 0
  clashes, 0 exposure, 1 intended moved clash (`loopHost_contracts`), 0 package hits. Against
  MIG-0b's landing set (15 files, 1,211 declarations): 0 full-name matches, 0 shared last
  components.
- **Widths and style**: 0 lines over 100; lint 0 FAIL, 2 WARN over 3 files.
- **Consumers** (code citations): the 53 rows **221 in 35 files**, the 34 home rows **216 in
  33**.
- **R3 sites**: 24 checks confirmed, 0 mismatches, the same lines: each of the 9 table rows'
  declaration line (6 distinct), the 5 code sites and the 10 docstring lines.

Changed since round 1:
- **Docstring mentions** of the 63 measured names: **194** (round 1: 191). The three new ones
  are `FormulaKit/Emit.lean:19` and `:29` (`exists_emitLoopTM`) and
  `RAMSimulation/WordSize.lean:75` (`computesFunInTime_lengthBits_spaceUsed`).
- **Replay closures**: whole, S and F-A **212**, F-B **82**, F-C **97**, F-D **34**, of **632**
  modules (round 1: 206, 80, 91, 30 of 624).
- **Deletion plan**: the two rows above.

**The consumer delta.** PRs #85/#86 cite `exists_emitLoopTM` and
`computesFunInTime_lengthBits_spaceUsed` only in docstrings, so the per-row code-citation totals
are unchanged (consumers log). `WordSize.lean:75` names `Build/Catalog.lean:4318`; the row stays
in Catalog, but that line number goes stale at F-D. **F-D gains one docstring site**, in a file
of the RAM-simulation stage.

**The replay delta.** The eight new modules are `FormulaKit`, `FormulaKit/Emit`,
`FormulaKit/Gate`, `RAMSimulation`, `RAMSimulation/{Classes,Simulation,WordSize}` and
`Programs/WordRAM/Extended`. Six import a MIG-1 file: S/F-A +6, F-B +2 (the formula kit), F-C
+6, F-D +4 (the RAM simulation).

## Finding 2: the runner and the builder

- **`runall.sh`**:
  - `set -euo pipefail`;
  - every input is checked before anything is written (exit 2);
  - `elab` returns the elaborator's status, and counts errors, sorry warnings and other
    warnings;
  - each check compares its measured line with `expected-r2.json`; a deviation is recorded,
    reported and continued past, so one run shows all deviations;
  - the identity control must exit with exactly 3 (identity.py exits with its failure count)
    and name exactly the three expected declarations;
  - failures go to stderr, so no check output is mistaken for a result;
  - the run exits 1 on any deviation;
  - the overlay, the retarget checks, the deletion plan, the R3 sites and the decision-2
    records are part of the same run.
- **`build_unit.py`** (diff `r2/scripts/build_unit.py.diff`):
  - it refuses, before writing: a missing parts directory, an empty template set, a set of
    another size than `--expect`, a duplicate `.lean`/`.lean.txt` pair, a missing source file,
    a failed `mkshim.py` call;
  - it assembles in memory and replaces its output through a temporary file;
  - its output for the round-1 templates is unchanged (the byte-identical unit).
- **Negative controls** (runner-negative-control log):
  1. the runner on a scratch copy whose only change is one token of the Composition template
     (`w.length + 1 ↦ w.length + 0` in `constTM_computes`): **exit 1**, 14 deviations,
     among them the unit's 5 errors, five cut checks, identity, the control count and the
     axioms;
  2. the runner on a scratch copy without `data/consumer-names.json`: **exit 2** before
     writing anything (no `logs/`, `work/` or `cuts/` created);
  3. inside every run, `build_unit.py` on an empty template set: exit 2, its target file
     untouched.

## Finding 3: the bundle

`r2/BUNDLE-FILES.txt` lists every path. Since round 1 it adds the manifests themselves, the
9 + 2 + 1 templates, `campaign_style_lint.py`, `consumer-names.json`, the round-1 scripts and
data that the runner re-uses, the overlay and its diffs, the retarget checks and table, and all
14 round-2 logs.

`r2/BUNDLE-MISSING.txt` states what a rebuild still needs from outside the bundle: the tip's
checkout and olean snapshot, and MIG-0b's landing set. MIG-0b's set is not in the repository as
files: its `Finite.diff` is bundled, and the five new `Contract/*` files come from MIG-0b's
committed `build.py`.

`r2/EVIDENCE-MAP.tsv` maps every runner input to its repository file; the 36 round-1 inputs are
byte-identical to the committed files (checked).

## Corrected descriptions (finding 4; the round-1 pack's text, now superseded)

1. Repository-side attestations, "Style". Read: **"`scripts/campaign_style_lint.py` (a copy of
   the repository's) gives 0 FAIL and 2 WARN over 3 files, as logged: the unit (2,950 lines)
   and the spec probe (4,112 lines) exceed the 1,000-line threshold; the bridge probe has none
   (user rule: size alone is no reason to split)."** It replaces "0 FAIL and one WARN per
   elaboration unit".
2. Decisions in force, the style rationale. Read: **"(MIG-0b round-2
   `audits/evidence/mig0b/r2/NOTES-r2.md` §3 and §10 item 6, in the repository and
   bundled)"**. It replaces "(MIG-0b round-2 `NOTES-r2.md` §3 and §10 item 6, not yet in the
   repository; `BUNDLE-MISSING.txt`)". MIG-0b round 2 has since closed (`6b5345cb`).
3. Changes from the draft, item 14. Read: **"The R3 retirement uses two endpoint lemmas
   (design §7), proved here. The two retired rows with code consumers, `copyTM_run` and
   `transferTM_run`, are each re-derived from them in four lines (`MIG1Gate.retired_*`), which
   is the consumer edit; the other four retired rows have no code consumer."** It replaces
   "each retired row is re-derived from them in four lines".

## Brief for the auditor

Restate each new or changed statement in your own words before reading its docstring: the
strengthened `loopHost_prepare`; the moved `loopHost_contracts`; `loopCall_heads`,
`segment_heads`, `space_radius` and `seamed_space`; the stand-in. Argue each true in 2–5
sentences or give a counterexample. Attempt at least six adversarial instantiations (failure
modes of `audits/TEMPLATE.md`); candidates are in item 2. Points to rule on:

1. **Finding 1's repair, by the overlay.** Check that:
   - part 1 differs from the tip's `Loop.lean` only as in the hunk table
     (`part1-vs-tip.diff`);
   - the new clause is proved for the actual fuel endpoint, in both `forward` modes, from
     `u ≤ T |x|` and the interval lemma at the initial configuration;
   - the stand-in is MIG-0b's lemma (`standin-vs-mig0b.diff`; MIG-0b's `Finite.diff`);
   - the moved contract is Catalog's text under the stated retargets and the
     explicit-coefficient transform, with no `f2_`/`a2_` name;
   - part 2's six proofs use the moved declarations, not shims;
   - the overlay imports only Loop's imports and `Simulation`, and not `Loop`;
   - the elaboration counts and the 23 axiom prints hold, and the warning multiset equals the
     tip's.

   Is a full copy of `Loop`, elaborated in Loop's closure, an adequate pre-landing check of
   F-C's Loop edits? The F-C replay (97 modules) remains the fill gate's obligation.
2. **The new statements, adversarially.** Candidates:
   - `loopHost_prepare` with a fuel machine of zero work tapes (the clause is vacuous);
   - `forward = true`, the emitting host;
   - `T |x| = 0` (then `hF` cannot hold: the initial state is live);
   - heads moving left of the origin;
   - the contract at `R |x| = 0`, and with an accepting last candidate (the terminal is the
     halted copy of seam `R + 1`, whose heads are bounded by `T`);
   - `segment_heads` at `N = 0`, and with an early halt;
   - `space_radius` at `B = 0`;
   - the budget arithmetic `2(T + 10(T + 1)) + 1 ≤ 23(T + 1)` at `T = 0`.
3. **The retarget table** (`retarget-table.tsv`). Is the population complete (moves and
   absorptions; statements as well as proofs scanned), and are the classes sound? Challenge:
   - NOT-CARRIED: are the seven replaced proofs really independent of region names?
   - the accessibility rule: private only within a home, public within the import closure, and
     the decision-4 condition;
   - the claim that no inaccessible retarget exists.

   Check the Lean examples and their negative control. Does restricting the tip control to
   Loop-sourced copies leave a gap? The non-Loop non-verbatim copies are 3 absorbed split
   lemmas and `f2_splitBody_round`, which is statement-identical.
4. **The runner and builder fixes, and the bundle.** Read `runall.sh` against finding 2's list
   and check the three negative controls. Does `BUNDLE-FILES.txt` cover what the reproduction
   needs, and is `BUNDLE-MISSING.txt` honest about MIG-0b's landing set?
5. **The corrected descriptions** (finding 4): are the three sentences right?
6. **The re-measurement.** Check the ten files unchanged (blob ids, provenance log), the byte
   identity of the rebuilt unit, and the counts. Are the replay and docstring deltas fully
   explained by PRs #85/#86? Is the new F-D docstring site (`WordSize.lean:75`) right?
7. **The decisions' records**: decision 2's sorry-free batches (a text scan, not a kernel
   check); decision 3's two consequences (`f2_head_steps`'s fate, the 70 landed names); the F-C
   description.
8. Report anything else that the overlay, the table, the runner, this pack or the round-1 pack
   (as corrected) misstates.

## Repository-side attestations (verify or challenge)

All MEASURED, from the round-2 logs; one runner pass unless stated.

1. **Environment.**
   - Every elaboration went through `tools/leanelab.sh`: `lean <file>` with `LEAN_PATH` set, no
     `-o`. No olean was written: `find oleans-t1 -newer <first round-2 script>` is empty.
   - No `lake`, no network. Python ran as `python3 -I`.
   - Git was used read-only: for the provenance log (`rev-parse`, also for blob ids
     `<commit>:<path>`; `diff --stat`, `log`, `status`) and for filling this pack's commit
     hashes (`rev-parse`, `log --grep`, `cat-file -e`, `merge-base --is-ancestor`). The
     worktree is clean and its index file's mtime is unchanged. No hash was typed by hand.
2. **The runner.** `runall.sh` at the tip: exit 0, `RESULT: PASS`, every check matching
   `expected-r2.json`. The two changed expectations (replay closures, module count) are
   explained in that file's `_note.replay` and above. The negative controls: exit 1 (14
   deviations), exit 2 (nothing written), and the builder refusal leaves its target untouched.
3. **The overlay**: as under "Result" above. **The maintainer re-elaborated it** with the same
   tool, checkout (`99ad2f98`) and snapshot (`oleans-t1`): exit 0, 0 errors, 0 sorry warnings,
   61 other warnings; all 23 `#print axioms` lines within `propext`, `Classical.choice`,
   `Quot.sound`. The strengthened `loopHost_prepare` states Catalog's fuel-head clause over
   both `forward` modes.
4. **The retarget checks**: 21 examples and 0 errors after part 1; exactly 2 errors after the
   tip's `Loop.lean`, inside the `f2_loopHost_prepare` and `f2_loopHost_contracts` examples.
5. **The retarget table**: 59 declarations, 215 citations. Classes 53 / 112 / 11 / 1 / 38 / 0;
   accessible 174, after F-A 3, not carried 38, inaccessible 0.
6. **The deletion plan**: round 1 reproduced byte for byte at the tip; round 2 differs in the
   two rows above; 378 declarations, 9,172 docstring-inclusive lines, 0 unassigned.
7. **Unit, probes, identity, axioms, names, style, consumers, replay, R3**: as in the
   re-measurement section.
8. **Decision 2's records**: as in the table under the decisions (s-records log).
9. **Not established here**: the F-C landing compile and its 97-module replay; the application
   of the in-place renames; the S, F-A, F-B and F-D batches beyond the re-measured statements.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/mig1-statements-r2-findings.md`. The gate closes when this round reports zero blockers
and zero majors; stage S then lands as described, and each fill batch has its own gate.
