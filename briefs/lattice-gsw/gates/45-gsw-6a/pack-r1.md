# Gate 45 · the GSW 6a gate: O1 (#358) and the 6a statements (#359) · round 1

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). This is **Gate 45**
of the phase-6 rulings (P6-Q1: the complexity-layer statement gate of GSW phase 6, "6a"), with the scope plan section r3
§H7 gives it: the owner-side PR O1 and the 6a statement PR. Two stacked PRs are audited.

- **PR #358 (O1)**: draft [PR #358](https://github.com/Shilun-Allan-Li/tcslib/pull/358) at
  `a616adcac0760ab56b1b0a2a4869f4763843f9ab` (branch `land/gsw-6a-o1`), base `cryptography/pass-shelat-ch2-4`. Its merge
  base is `e1d39836ed4a69a34914c35f4c73c71de853dcc6`, the records tip at the re-cut. One SSH-signed commit: the maintainer's
  `git cherry-pick -S` of the worker's `413e9aa42f6b96b4d65673c37c83819b2fb77579` (author kept), tree `a461632b…` =
  `git merge-tree e1d39836 × 413e9aa4`. It changes 4 files (+279/−184). GitHub's REST `base.sha` for #358 is
  `3ef91b408b2a9303fa36c8ac696da532e4170ed0`, a records-only descendant of `e1d39836` (0 code paths; `checks/series.txt`).
- **PR #359 (statements)**: draft [PR #359](https://github.com/Shilun-Allan-Li/tcslib/pull/359) at
  `73aedcdaaaffef7e69ab012d9b9195f150bae68d` (branch `land/gsw-6a-statements`), **stacked on #358**: base `land/gsw-6a-o1`
  at `a616adca`. Six SSH-signed commits: maintainer cherry-picks of the worker's five commits `ad8e170f..ec36703b` (author
  kept; `~1` has tree `541eb26b…` = `git merge-tree e1d39836 × ec36703b`) and the maintainer's landing edit **LE-ren**
  (`73aedcda`, tree `2c243bb1…`). It changes 17 files (+3383/−2).
- **Records pin:** `8c5875fa268a622e4e166da5f7a992715097c2c7`, the tip of `origin/cryptography/pass-shelat-ch2-4` after
  `git fetch` at staging ("Records: GSW 6a re-replay on snapshot #5; draft PRs #358, #359"). It is `e1d39836` plus five
  records-only commits (0 code paths, `machine-library-design.md` included), and pin × #359 (tree `ab4aff19…`) differs from
  the pin in exactly the 18 series paths (`checks/series.txt`). Every record this pack cites is read at the pin; this pack's
  own files are filed after it.
- **Lean base.** `e1d39836`'s Lean equals `3f540c22360c869069a0fba684e23ce6f3cb20db`, the #346 merge, whose tree is **olean
  snapshot #5**. The diff `3f540c22..e1d39836` over `TCSlib`, `TCSlib.lean`, `audits`, `scripts`, the lake files and
  `lean-toolchain` is empty.
- **Scope:**
  - **#358** is audited **as a proof/refactor**: the move of the balanced-tree combinators (`TreeNCAC.combine`, `pairUp`,
    `combineFuel` and their lemmas) from `TreeNCAC.lean` into `Complexity/CircuitComplexity/FormulaArith/Combinators.lean`
    as the public `BoolCircuit.TreeCircuit.balanced` with five lemmas and two readers, the facade `FormulaArith.lean`, and
    `TreeNCAC`'s re-pointing with every statement unchanged.
  - **#359** gets a **statement-fidelity audit of all 98 targets** against the sources (Bar89, BV14, BV11) and plan r3,
    with every hypothesis checked for vacuity or falsity and the edge cases, and an audit of the definitions, the proved
    readers and helpers (part of the audited surface; `workflow.md` §2), the registrations, the citations and the
    sketches.
- **Out of scope** (do not audit; mention only if something in #358/#359 depends on them):
  - the **Q3 owner-side reader PR** (the nine readers plus `gadgetCorrect_iff` of G6A-F03), which is separate and lands
    before the fills; and **any in-house 6a fills** being prepared overnight under the overnight ruling (decision-log row
    "Overnight ruling (Seyoon): in-house prep plus small fills"). Neither is on either PR;
  - **6b** (the GSW cryptography: bootstrapping, circular security, the leveled scheme, O2), which is **Gate 46**. This
    gate checks the 6a statements against what r3 §H5.9–H5.16 plans to consume, but not the 6b statements;
  - **[Gen09]**: by P6-Q19 (refined) the Gen09 citation is a docstring-only follow-up for 6b; no 6a file cites it
    (`checks/tags.txt`: 0);
  - #357 (Gate 48), #347 and #355 (cleanup) except for the merge interaction below, which is a maintainer merge condition.

Lean paths below are under `TCSlib/Complexity/` unless they start with `TCSlib/`; `BP/` is `BranchingPrograms/`, `CC/` is
`CircuitComplexity/` and `FA/` is `CircuitComplexity/FormulaArith/`.

## What changed

Lines are base → head (`checks/sizes.txt`, `source-head-r1.json`).

**#358** (base `e1d39836`):

| File | Status | What | Lines |
|---|---|---|---:|
| `FA/Combinators.lean` | new | `TreeCircuit.balanced` and its lemmas, `pairUp`/`combineFuel` private, moved from `TreeNCAC` | 246 |
| `CC/FormulaArith.lean` | new | facade | 23 |
| `CC/TreeNCAC.lean` | changed | imports `Combinators`; the moved block removed; `toBinary`'s body and four proof lines re-pointed to `balanced` | 537 → 359 |
| `CircuitComplexity.lean` | changed | one import and its contents line | 322 → 326 |

- **Public API:** `balanced`, `balanced_eval`, `maxFanin_balanced_le` (`≤ max 2 (maxFaninL cs)`), `depth_balanced_le`
  (`≤ maxDepth cs + ⌈log₂ |cs|⌉ + 1`), `size_balanced_le` (`≤ sumSize cs + |cs| + 1`), and the `rfl` readers `balanced_nil`,
  `balanced_singleton`: decls2 **7 ADDED / 0 CHANGED / 0 REMOVED** (checkpoint 1, at the issue base `f6f295a6`; #358's
  four files and both pre-existing bases are blob-equal to that run's, `checks/blobs.txt`). The removed `combine*` were
  private, so decls2 does not list them.
- **The five Rule 10 repairs** (ruled **6a Q2 A**): the three brief-named `simp [TreeCircuit.eval]` reads of `TreeNCAC`
  (base `:195`, `:199`, `:261`) now go through `eval_node_true`/`eval_node_false` (`TreeDAG.lean:126/132`, with
  `List.all_cons`/`any_cons` for `foldr_cons`), and the nil cases of `sumSize_pairUp` and `maxFaninL_pairUp` go through
  `sumSize_nil`/`maxFaninL_nil` (`Basic.lean:235/242`) instead of definitional unfolding. Otherwise the moved proofs are
  unchanged apart from three whitespace re-wraps of base lines over 100 and the five promoted docstrings
  (checkpoint-1 review § *O1 content*).
- **What stays in `TreeNCAC`:** 2 pre-existing seal failures (`maxDepth_map_le`, `maxFaninL_map_le`, byte-identical
  declarations and error messages at the tip) and 4 pre-existing explicit foreign unfolds (`:188` `eval_node_map`, `:228`,
  `:250`, `:268` `toBinary_*`); both are **G6A-F05**, pre-existing and not O1's. At the tip the file fails 4 times (also the
  two nil cases O1 repairs) and has 7 foreign unfolds (also the 3 O1 removes).

**#359** (base `land/gsw-6a-o1` = `a616adca`):

| File | Status | Targets | Lines |
|---|---|---:|---:|
| `BranchingPrograms.lean` | new facade | 0 | 39 |
| `BP/Defs.lean` | new: the general model `BranchingProgram w n` (`Fin w → Fin w` maps), `IsPermutation`, `yield`, `conj`, `complementLast`, `BranchingProgramFamily`, `InBWBP`, `InPBP` | 11 (C1–C4) | 412 |
| `BP/Eval.lean` | new: the host `evalWith` (H18), `Instr.stepWith` | 5 (C5–C8) | 172 |
| `BP/Barrington.lean` | new: `IsFiveCycle`, `FiveCycleRecognizes`, `sigma1/2`, the computable conjugator, `commutatorProgram`, `barrington` | 11 (C9–C16) | 463 |
| `BP/BarringtonConverse.lean` | new: `Instr.wire`, `wireComp`, `compTree`, `toFormula`, `topDepth` | 11 (C17–C21) | 304 |
| `BP/NC1.lean` | new: the class corollaries | 5 (C22–C25) | 135 |
| `CC/NANDForm.lean` | new: `DAGGate.IsNAND`, `IsNANDForm`, `nandGadget`, `toNANDForm` | 6 (N1–N6) | 284 |
| `CC/NANDLayering.lean` | new: `IsLayered`, `litInput`, `layerChain/At/Column/Fold`, `layerGates`, `layerOutput`, `layerNAND` | 7 (N7–N13) | 388 |
| `FA/Combinators.lean` | changed (O1's file + a pure insertion of F1–F3, then LE-ren) | 24 (F1–F3) | 246 → 629 |
| `FA/CarrySave.lean` | new | 7 (F5–F6) | 297 |
| `FA/Compare.lean` | new | 7 (F7–F8) | 238 |
| `FA/ModSum.lean` | new | 4 (F9–F10) | 196 |
| `CC/FormulaArith.lean` | facade contents | 0 | 23 → 31 |
| `CircuitComplexity.lean` | imports, contents | 0 | 326 → 334 |
| `TCSlib/ComputationalModels.lean` | 1 import, 2 models, 4 conversions, [Bar89] | 0 | 144 → 165 |
| `TCSlib.lean` | `import TCSlib.Complexity.BranchingPrograms` | 0 | 89 → 90 |
| `machine-library-design.md` | §14 status, rows H18–H20, subsection "Circuit and formula gadgets" | — | 4005 → 4037 |

- **98 targets, 98 `sorry`** (`checks/targets.txt`: every target located at the head, file:line; per file 11/5/11/11/5/
  6/7/24/7/7/4; 98 lines whose code is `sorry`, one per target). The delivered row map (`delivery/evidence/stmt/
  rowmap.txt`) lists 100 admitted rows; LE-ren removed `rename_eval` and `depth_rename`.
- **Everything else is proved**: 71 definitions, 3 structures and 110 proved theorems in the delivered row map (minus
  LE-ren's `rename` and `rename_eq`): definitional readers (`_eq`, `_iff`, case lemmas, `simps` field equations), glue
  such as `isPermutation_iff`, `getD_conjugatorTable`, `conjugator_apply_of_bijective`, `Instr.isPermutation_ofPerm`, the
  four decidability instances (G6A-F08), and the disclosed public helpers `layerChain`/`layerAt`/`layerColumn`/
  `layerFold`, `conjugatorIndex`/`Fun`/`Table`, `commutatorProgram`, `csaLayer`, `constBits`, `maskedConst`, `language_eq`
  (`delivery/evidence/stmt/definitions-readers.txt`). decls2 tip → #359 head: **267 ADDED / 0 / 0**, which is #358's 7
  plus #359's **260** (`phase2/statements/decls2-tip-vs-head.tsv`).
- **LE-ren** (ruled **6a Q1 A**; G6A-F01): `TreeCircuit.rename` (`Combinators.lean:368` as delivered) was extensionally the
  public, proved `TreeCircuit.reidx` (`TCSlib/BooleanAnalysis/LMN/CircuitReindex.lean:24`), and the targets `rename_eval`,
  `depth_rename` restated the proved `reidx_eval`, `reidx_depth`. LE-ren drops `rename`, `rename_eq`, `rename_eval`,
  `depth_rename` and points the module docstring, the facade contents and the registry row to `reidx`. Its hunks are
  identical to phase 1's `landing/LE-ren-proposed.diff` (`checks/le-ren.txt`: 6 hunks, RESULT IDENTICAL), and `git grep`
  finds no `rename`-family reference in `TCSlib` at the head. Admissions 100 → 98; `Combinators` 659 → 629. The dedup entry
  **DL-54** (move `reidx` and its two lemmas into `Combinators`, owner-side, re-pointing `widenCircuit`) stays open
  (`records/duplication-ledger-DL54.md`). The fourth cherry-pick's message still lists `rename`; LE-ren supersedes it
  (disclosed in the PR description).
- **Non-target constants with `sorryAx`** (`checks/sorryax-dependents.txt`): exactly five, reached only through N2 or
  N12–N13:
  - **`toNANDForm`** (`NANDForm.lean:234`, a `def`): `C.rewrite (nandGadget n) nandGadget_correct hC`, passing the admitted
    N2 proof as a `Prop` argument of `DAGCircuit.rewrite`;
  - **`toNANDForm_eq`** (`:240`, an `rfl` **theorem** whose statement names `nandGadget_correct`);
  - **`layerNAND`** (`NANDLayering.lean:315`, a `def` building a `DAGCircuit (n + n)` whose `args_lt` and `output_lt` fields
    are the admitted N12 and N13);
  - **`layerNAND_gates`**, **`layerNAND_output`**: its `simps` field equations (**theorems**, not definitions).
  No definition body contains the `sorry` token; two definitions carry `sorryAx` through a proof argument. Plan r3
  (§H5.6, §H5.6b, §H7) and the brief's check 5 foresee exactly this for `toNANDForm` and `layerNAND`.

No other path changes: `DAGCircuit`, `DAGTransform`, `DAGFanin`, `TreeDAG`, `Basic`, `NCAC`, `Adder`, `Parity`,
`Hierarchy`, `LayeredDAG` and `LMN/CircuitReindex` are blob-equal at the base and the head; nothing under `Cryptography/`
or `blueprint/` changes.

## Rulings and records in force

1. **Phase-6 rulings P6-Q1..Q13 and the location ruling** (Seyoon, 2026-11-16; `records/…/phase6/rulings.md`): Q2
   Barrington's input model is `TreeCircuit n` (AND/OR formulas over literals with polarity), with `DAGCircuit` reached
   through the depth-preserving `toTree`; **Q3 both directions, BWBP = NC¹** (Thm 1 with Lemmas 1–3, the `DAGCircuit`
   corollary with length ≤ `4^depth`, NC¹ ⊆ poly-length width-5 PBPs, and Thm 2); **Q4 the general model of Bar89 §1**
   (maps `[w] → [w]`) with `IsPermutation`, instructions `⟨var, f0, f1⟩` in BV14's order (Bar89's order disclosed),
   `yield` in program order, the public host `evalWith` with `evalWith_rel`, registered; Q5/Q6 the formula-arithmetic
   layer under `FA/` with O1 promoting `combine`; **Q9 NAND only** (BV14 Def 2.13) through a new conversion; **Q13
   `barrington` computable** (explicit conjugator). Location ruling: all of this lives under `Complexity/`.
2. **P6-Q14..Q19** (same day): **Q14 B** consecutive key chain plus a new generic **layering conversion** (double-NAND
   chains; parity twins for odd gaps, confirmed by Seyoon in the decision log); **Q16** NAND form is a predicate on
   `DAGCircuit` (every gate a `¬` gate of fan-in ≤ 2), the conversion an instance of `DAGCircuit.rewrite`, depth factor 2,
   NAND-form circuits not `IsWellFormed` (disclosed); **Q17** registry rows H18 (`evalWith`), H19 (`runWith`/`runWith_rel`),
   H20 (`DAGCircuit.rewrite`), whose contracts Gate 45 audits; **Q18** Thm 2's circuit is a fan-in-2 `TreeCircuit` formula
   reaching `InNC 1` through `InTreeNC.inNC`; **Q19 (refined)** Gen09 is docstring-only and not a bottleneck.
3. **Plan section r3** (`records/…/phase6/plan-section.md`, SHA-256 `06824b3db875e7388771b6f7a5e78d62bf7d77fa35571fc3a9deeebc329214fd`):
   §H3 design, §H4 modules and definitions, **§H5.1–H5.8 the statements** (C1–C25, N1–N13, F1–F3, F5–F10; F4 became O1),
   §H5.9–H5.16 the 6b consumers, §H7 "Gate 45 audits" (the checklist the auditor should cover), §H8 risks.
4. **The issued brief** (`records/…/issued-6a-r1/brief.md`): scope, checks 1–12, frozen files, delivery format.
5. **6a rulings Q1–Q4** (Seyoon, 2026-11-17; `final-6a-r1/review.md` § *Rulings*): **Q1 A** LE-ren (DL-54); **Q2 A** accept
   O1's five repairs; **Q3 A** one owner-side reader PR, separately and before the fills (out of scope here); **Q4 A** keep
   N12 in the `args_lt` field form.
6. **The overnight ruling** (Seyoon, 2026-11-17): the Q3 reader PR and in-house small fills are prepared as drafts,
   reviewed before any PR, and are **not in this gate**; "Gate 45 can still change the statements; any such change is
   re-checked."
7. **Rule 10** (brief check 6; `policy.md` §1 *Definitions land with their lemmas*): consumers never unfold another
   file's TCSlib definition; core and Mathlib definitions may reduce in `rfl`/`decide`/`show` steps; reducible
   abbreviations are notation and never requested; a projection `CoeFun`/`Coe` instance is notation (**coe-A canonical**;
   strict variants run and attributed). Inside a file its own definitions may be read directly.
8. **G44-01 precedent** (Gate 44, `records/briefs/pairings/gates/44-pairing-fills/findings-r1.md`): disclosure of a
   duplicate is not acceptance; an accepted duplicate needs a recorded acceptance and a ledger row with its repayment.
   G44-02: a source locator must name the result it cites. G44-03: per-variant counts must be exact.
9. **Signing** (BS-F08 precedent): Claude cloud sessions on this account share one commit-signing key, so a signature
   attests a session on the account, not the maintainer; provenance rests on the pinned hashes and the cherry-picks.

## Questions for the audit

**A. #358 (O1), as a proof/refactor**
1. Is the moved code the base's `TreeNCAC.lean:172–350` with exactly the stated changes (the five repairs, three
   whitespace re-wraps, five promoted docstrings, two new `rfl` readers) and nothing else? Compare `sources-r1.zip`
   `base-e1d39836/…/TreeNCAC.lean` with `o1-a616adca/…/Combinators.lean`.
2. Are the seven public statements true and do the moved proofs establish them, for every `b`, `cs` (empty and singleton
   lists included)? Are `maxFanin ≤ max 2 (maxFaninL cs)`, `depth ≤ maxDepth cs + ⌈log₂ |cs|⌉ + 1` and
   `size ≤ sumSize cs + |cs| + 1` the right bounds (r3 §H5.8)?
3. Are the five repairs semantics-free, and do the two extra ones (nil cases, Q2 A) read only published `rfl` readers?
4. Is every `TreeNCAC` statement unchanged (checkpoint 1's frozen check: 0 violations, 2 controls), and does `toBinary`
   still compute the same circuit?
5. Rule 10: `Combinators` 174 and `FormulaArith` 194 requests, 0 errors in all four variants; `TreeNCAC` 194 with exactly
   the 2 G6A-F05 failures; the facade 3659 (chunked) with 0 errors; paired controls on `balanced` (2), `sumSize` (4) and
   `maxFaninL` (4) sealed negatives per harness, each failing exactly once (`phase2/rule10/controls-summary.txt`). Is
   G6A-F05 correctly pre-existing and not O1's?
6. Docstrings and sources: the kept [AB09, p. 118] tag (a library tag with no ingest, as in `NCAC.lean`/`DAGFanin.lean`),
   the module docstring's "promoted unchanged" (G6A-F07: five repairs were made), the size and width of the new files.

**B. #359: fidelity of the 98 targets** (statement by statement; `checks/targets.txt` lists them with file:line)

For each target: is it **true** as stated, does it say what the cited source says (or what r3 states, with the deviation
disclosed), are its hypotheses satisfiable and **not vacuous or contradictory**, is it **not trivially weaker** than
what its 6b consumer needs, and are the **edge cases** right?
1. **The model, C1–C4** (`BP/Defs`) against Bar89 §1 (`p001-b002`, `p002-b001`) and BV14 §3.3: general maps with
   `IsPermutation`; `yield` in program order (`yield_append : (B₁ ++ B₂).yield x = B₂.yield x ∘ B₁.yield x`) against Bar89's
   product convention; `conj` (Bar89's θσθ⁻¹ replacement) and `complementLast` (post-composition with `σ⁻¹`, Lemma 2's
   last-instruction form); recognition by accepting sets; `InBWBP`/`InPBP` with the length bound `a·(n+1)^k`; the `n = 0`
   and `w = 0` cases.
2. **The host, C5–C8** (`BP/Eval`, H18): the push form `evalWith` with `Finset` sums, generic in selector and value type;
   C6 under `IsPermutation` against BV14 Eq. (4) (`p013-b002`); C7 `evalWith_rel` step-indexed; C8 one-hot to one-hot for
   general maps. Is the contract what r3 §H5.9 G2 (`homEvalPBP … (Pi.single s₀ (gadget P))`) needs?
3. **Barrington Thm 1, C9–C16** (`BP/Barrington`) against Bar89 Thm 1 and Lemmas 1–3 (`p003-b001..b005`, `p004-b002`):
   the commutator `(12345)(13542)(54321)(24531) = (13254)` translated to program order and checked by kernel `decide`
   (C9); the explicit computable conjugator with `θ(σᵏ 0) = τᵏ 0` and its fallback `1` off its domain (C10, P6-Q13);
   `FiveCycleRecognizes` including `IsFiveCycle σ`; C13's hypotheses `maxFanin ≤ 2` and a five-cycle; C14 `length ≤ 4^depth`
   for every `σ`, constants included (length 1, depth 1), and `length_pos`; C15; the OR case by De Morgan through
   `complementLast`; `[NeZero n]` for constants.
4. **C16 and G6A-F11.** `barrington_yield_zero` reads the start state `0`: accepted inputs end at `σ 0 ≠ 0`. Its
   deviation note says "BV14 reads coordinate 1"; the phase-1 review (G6A-F11) reads BV14 §3.3 (`p013-b002`) as outputting
   1 iff `ζ_L = 1`, the **start** state, i.e. the complement of the five-cycle reading, and calls the note harmless with the
   statement correct. Is C16 correct, is its deviation note accurate, and is the `σ 0` reading the one 6b's G3 must use?
5. **Thm 2, C17–C21** (`BP/BarringtonConverse`) against Bar89 Thm 2's proof (`p004-b003`) section by section: `Instr.wire`,
   `wireComp`, `compTree`, `toFormula`; C19's depth `(⌈log₂ w⌉+2)·⌈log₂ l⌉+1` and C21's `topDepth w = w⌈log₂ w⌉+⌈log₂ w⌉+3`
   (settled constants; G6A-F08); `w = 0`, `l = 0` and empty accepting sets; fan-in 2.
6. **NC¹, C22–C25** (`BP/NC1`): C22 from a `DAGCircuit` with `IsFaninTwo` (which includes `IsWellFormed`), `[NeZero n]`,
   a five-cycle output, length ≤ `4^depth`; C23 `InNC 1 → InPBP 5` with `n = 0` handled by the accepting set; C24
   `InBWBP → InNC 1` through `InTreeNC.inNC` (P6-Q18), with the depth `b·(log₂ n + 1)` and size `≤ 2^(depth+1)`; C25 both
   equalities against the Corollary (`p004-b004`). Are these the **nonuniform** classes Bar89 means, and do the class
   definitions (`InBWBP`, `InPBP`, `InNC`, `InTreeNC`) make the equalities non-trivial (no vacuous family condition)?
7. **NAND form, N1–N6** (`CC/NANDForm`) against BV14 Def 2.13 (`p008-b002`) and P6-Q16: `IsNAND`/`IsNANDForm`; N2
   `nandGadget_correct : GadgetCorrect n 2 (fun _ l => l ≤ 2) DAGGate.IsNAND (nandGadget n)` against `GadgetSpec`
   (`DAGTransform.lean:55`): value, cost ≤ fan-in + 2, ≤ 2 added levels, NAND outputs; N3 semantics; N4 form; N5 depth
   `2·depth`; N6 size `n + 4·#gates`; the domain `∀ g ∈ C.gates, g.args.length ≤ 2` (not `IsFaninTwo`); the
   not-`IsWellFormed` disclosure; no `NAndCircuit` clash (§H7).
8. **Layering, N7–N13** (`CC/NANDLayering`) against r3 §H3.13 and BV11 Thm 3.1 / Def 3.6 (`p015-b001`, `p014-b001`; a
   glue unit with no ingested source, r3 §H1 gap 4): `IsLayered` against level-by-level evaluation; `litInput` (inputs
   `x, ¬x`, `n + n` inputs, `[NeZero n]`); the column construction (base, parity twin, double-NAND chain; odd gaps); **N7
   only under `IsNANDForm`**, N8 with no hypothesis, **N10 exact depth**, N11 ≤ `2(D−δ)+1` gates per column, N12–N13 the
   two `DAGCircuit` fields. **N12 is stated in the `args_lt` field form** (Q4 A, G6A-F04) rather than r3's
   `GatesAcyclic (n + n) C.layerGates`: is the meaning the same (`DAGCircuit.lean:395` against `:465`)? The name
   `layerNAND` against `LayeredDAG.toLayered` (`:208`).
9. **Formula arithmetic, F1–F3, F5–F10** (`FA/*`) against r3 §H5.7 and the BV11/BV14 decryption-circuit passages:
   `neg` (De Morgan), `subst` (with `Finset.univ.sup` for r3's `⨆`, G6A-F08), `const`, `and2`/`or2`/`xor2`/`xor3`/`maj3`;
   `csaStep` (the full-adder identity bitwise) and `csaReduce` with `csaLevels_le` (F6 `2⌈log₂ k⌉`); `carryOut` as
   generate/propagate (F7 `2⌈log₂ b⌉+3`, with `carryOut`'s explicit `b`); `geConst` (F8, `+7`) for **every** constant `c`
   (the top-bit argument with `p = max|U| |W|+1`); `modSumInterval` (F9: `S < max M 1 · q ≤ 2^w`, the unique witness
   `j = S / q` when `hi ≤ q`, the `q = 0` and `M = 0` cases, and the kept unnecessary `lo ≤ hi`, G6A-F09);
   `modSumDepth_le` (F10, r3's closed form verbatim, no term linear in `log q`).
10. **The 6b consumers** (r3 §H5.9–H5.11; not audited, only used as the yardstick): do G2/G3 (`evalWith`, Barrington,
    `σ 0`), G5–G8 (the decryption formula from F9 and the gadgets, `decDepth`), G9–G10/G18 (NAND-only bootstrapping
    through N3/N4, layered circuits through N7–N13 for the consecutive key chain of Q14 B) find in 6a statements of the
    form and strength they need? A 6a statement that is true but too weak for its planned consumer is a finding.
11. **Definitions.** Are any definitions `sorry`'d? (Source: none; `sorryAx` reaches `toNANDForm` and `layerNAND` only
    through their N2/N12–N13 proof arguments; see § *What changed*.) Is that acceptable for a statement phase, given
    `workflow.md` §2 ("definitions and sorried statements only") and the plan's explicit design? Does any definition
    compute the wrong object, or depend on a target's truth for its value rather than only for a proof field?
12. **Readers and helpers** (proved, part of the audited surface): is every public definition published with a reader
    (`policy.md` §1), are the `rfl`/`Iff.rfl` readers exact, and are the four decidability instances and the disclosed
    public helpers correct and placed right? Are G6A-F08's **16 disclosed changes** against r3 (REPORT §6:
    `List.formPerm` for `c[…]`, `Finset.univ.sup` for `⨆`, `carryOut`'s explicit `b`, implicit binders, explicit formulas
    where r3 named lemmas, fan-in lemmas, public helpers with readers, the conjugator table, and the settled constants
    C21 `+3`, F6, F7, F8) all meaning-preserving?
13. **Traces (G6A-F14).** 89 targets reach only themselves; 9 targets whose statements name `toNANDForm`
    (`toNANDForm_eval`, `_isNANDForm`, `_size_le`, `_depth_le`) or `layerNAND` (`layerNAND_eval`, `_isNANDForm`,
    `_isLayered`, `_depth`, `_size_le`) also reach N2 or N12–N13 through those definitions. Is that the only cross-target
    dependence, and is it acceptable for the fills (N2, N12, N13 must be filled before those 9 are sorry-free)?

**C. #359: sources, citations, docstrings, sketches**
1. **The 112 citation anchors** (`checks/tags.txt` at the head: Bar89 95 tags, BV14 32, BV11 22, AB09 84 including
   pre-existing ones; `pNNN-bNNN` anchors 112; `phase1/citations/citecheck.out`: 112 ANCHOR OK, 18 QUOTE OK, 6 NOTFOUND
   that differ only in rendering, each read against the ingest in `phase1/citations/manual-quotes.txt`). Does each anchor
   point at the passage that supports the claim (not just an existing block), do the locators name the right results
   (G44-02), and are the quotations faithful (the "yielded by a each instruction" *sic*)?
2. **Reference lines** (G6A-F07): [Bar89] reads "D. A. Barrington … J. Comput. Syst. Sci." in `NANDLayering.lean:85` and
   `ComputationalModels.lean:159`, against "D. A. Mix Barrington … J. Comput. System Sci." in the five `BP/` files and the
   facade; the latter matches the ingest. Other G6A-F07 nits: `depth_subst_le`/`maxFanin_subst_le` call O1's import closure
   "(frozen)" (`Combinators.lean:382`); the module docstring's "promoted unchanged".
3. **Sketches** (`policy.md` §3): every target has a `**Proof sketch.**` naming its obligations. Several sketches name
   readers that are **missing at the base and proposed** (G6A-F03: `Lit.eval_eq`, `TreeCircuit.depth_lit`/`maxFanin_lit`/
   `size_lit`, `carryBit` case readers, `DAGCircuit.isWellFormed_iff`, `Language.inTreeNC_iff`, the `TreeCircuitFamily`
   readers, `gatesAcyclic_iff`, `gadgetCorrect_iff`), to come from the out-of-scope Q3 reader PR. Is each sketch sound
   given those readers, and does any sketch silently rely on an unfold Rule 10 forbids?
4. **Registrations** (Q4, Q17): `ComputationalModels.lean` lists both models and the four conversions; H18–H20 and the
   gadget subsection in `machine-library-design.md` (`pr359.diff.txt`): does every line reference point at the named
   declaration (H18 `Eval.lean:65/73/83/89/99/108/124/143/167`, H19 `DAGCircuit.lean:149/625`, H20
   `DAGTransform.lean:68/246/263/269/273/278/286`), and are the contracts as listed true?
5. **Sizes** (G6A-F06): every file under 1,000 lines; only `Combinators` (629) is above the 600 target, with 24 targets
   and r3's U8 projecting about 800–880 lines filled; the brief's U8 splits the gadgets into `FA/Gadgets.lean` if the fill
   passes 800. Acceptable?

**D. #359: duplication and reuse** (`policy.md` §1 *Duplication*; G44-01)
1. Is LE-ren complete (no other restatement of `reidx`, `widenCircuit`/`restrictCircuit` in `Hierarchy.lean:110/139`), and
   is DL-54 a correct ledger entry (no duplicate landed; the move of `reidx` is a dedup-queue item)?
2. Any other restatement of a public TCSlib lemma or a Mathlib fact (e.g. `Equiv.Perm.isConj_iff_cycleType_eq` behind C10,
   not restated because Q13 rules a computable conjugator; `Parity.lean`'s private dual-rail XOR, re-pointed later per
   P6-Q6; `FormulaKit/Gate.lean`'s CNF gates, a different model; `bitsVal`/`prefixVal`/`carryBit` reused as semantics)?
   An undisclosed duplicate is a major.
3. Clashes: 281 new names (18 private), 11 sharing a full name with O1's private moves out of `TreeNCAC` (whose tip copies
   O1 removes), 0 others; no `NAnd`, no `toLayered` clash; Mathlib has no `BranchingProgram`, `InBWBP`, `InPBP`,
   `FiveCycleRecognizes`, `IsFiveCycle`, `litInput`.

**E. Evidence and the carry-forward argument**
1. **Replays on snapshot #5** (phase2.md § *Re-replay on snapshot #5*; `rereplay5/`): R1 (#358 on snapshot #5) **9/9** rc 0,
   0 `error:`/`error(`, state **1429/1429**; R2 (#359 on R1) **20/20** rc 0, 98 warnings all `declaration uses 'sorry'`,
   state **1440/1440**; every rebuilt olean link count 1; admissions **+0** (R1) and **+98 EXACT** (R2: 98 targets, 98
   admitted, 98 matched, 0 extra, 0 twice, 0 missing; delta files identical to phase 2's); axiom probes byte-identical to
   the #4 runs (O1 141 constants, standard only; statements 544 constants, `sorryAx` in exactly the 98 targets and the 5
   dependents, no other non-standard axiom); **canonical coe-A re-run on 20 owner records** (O1's 4 on R1, the 16 of the
   R2-5 table on R2; the four O1 owners appear in both) with requested count, request name set, probe and source SHA-256,
   closure-module count and outcome **SAME** as phase 2's (`rereplay5/carry/sealcmp-*.txt`: RESULT ALL SAME); **root
   coe-A 14,074 requests, 15 chunks, 0 errors** (#4: 13,991; the 83 added names all homed in #340/#346 files,
   `rereplay5/carry/root-requests-vs-4.txt`). Do these bind to the two PR heads (REV, trees `a461632b`, `2c243bb1`)?
2. **The carry-forward argument.** Not re-run on #5: the strict A/B and coe-B seals of the 20 owner records, the paired
   controls (strict and coe; O1: 10 sealed negatives per harness; statements: 92), the delivery's 30 paired controls
   (30/30 on #4), and the explicit-unfold scans. The argument: (a) every non-root owner's closure key is equal at the old
   (#4) and new heads (`rereplay5/carry/ownerkeys-o1.tsv` 4/5 EQUAL, `ownerkeys-stmt.tsv` 16/17 EQUAL; only the root
   `TCSlib` differs, by the 5 modules of #340/#346), so each owner's source closure is byte-identical to the one sealed on
   #4; (b) the canonical coe-A re-run reproduces phase 2's request sets, probes and outcomes exactly; (c) the strict and
   coe-B request sets come from the same collector output, and the controls from those records; (d) every reused tool is
   byte-equal to its phase-2 copy (`rereplay5/tools/TOOLS.txt`; `checks/tools-carry.txt`: all 26 rows match a copy in the
   phase-1 or phase-2 ZIP by SHA-256); (e) the only owner whose closure changed is the root, and root coe-A was re-run.
   **Confirm or refute** that equal closure keys plus identical coe-A records stand in for re-running the strict/coe-B
   seals and the controls. Is anything in those results a function of something outside the owner's closure (Mathlib
   and the toolchain are fixed), e.g. the root, environment variables, or the snapshot's oleans for modules outside the
   closure?
3. **Exact per-variant counts** (G44-03): phase 2 R2-5's table gives `ComputationalModels` 1106/1107/1106/1107 (A/B/coe-A/
   coe-B) while every other owner has equal counts in all four variants; the delivery's root counts were 13,762/13,763/
   13,761/13,762. Check these against `phase2/rule10/stmt/seals-*.tsv` and the delivery, and say whether the asymmetry is
   explained.
4. **Integrity:** the delivery manifests (2137/2137, `evidence/` 2105/2105), `git am` reproduction of all six worker hashes
   at the issue base, `src/` equal to the delivered tree, decls2 271 → 267 after LE-ren, the 1,345 build logs recounted,
   the 30 delivered controls (`delivery/evidence/rule10/controls/`).

**F. Disclosures to grade.** Grade the phase-1 and phase-2 review findings **G6A-F01 to G6A-F15** in a separate table
(agree, or regrade with the reason), in particular F04 (N12 field form), F05 (pre-existing `TreeNCAC`), F06 (size), F08
(16 changes), F11 (`σ 0`), F14 (traces) and F15 (the driver edited mid-run).

## The replays (maintainer, 2026-11-17)

| | #358 (R1) | #359 with LE-ren (R2) |
|---|---|---|
| Phase 2 on snapshot #4 (05:31–07:45 UTC) | `a57dcf77`: 9/9, state 1424/1424 | `66036926`: 20/20, state 1435/1435 |
| Re-cut onto `e1d39836` | `a616adca` (range-diff 1/1 `=`) | `73aedcda` (range-diff 6/6 `=`) |
| Re-replay on snapshot #5 (07:41–09:45 UTC) | 9/9, state 1429/1429 | 20/20, state 1440/1440 |
| Admissions vs the tip | +0 | +98 EXACT |
| Axioms | 141, standard; log = #4's | 544; `sorryAx` 98 + 5; log = #4's |
| coe-A seals (re-run) | 4 owners SAME as #4 | 16 owners SAME as #4; root 14,074 / 0 errors |
| Strict A/B, coe-B, controls, scan | carried from #4 | carried from #4 |
| Lint (`campaign_style_lint --check8b`, `style_lint`) | FAIL/WARN sets = the tip's; 0 in new files | the same; 11 pre-existing findings |

- Snapshot #5 (`snapmap.py verify` against `olean-snapshot.map-3f540c22.tsv`): 1458 files, 0/0/0, at the start, after R1,
  after R2 and at the end. No `lake build`, no cache get; modules through `scripts/lean_check_tree.sh`, seals and probes
  through `lean -DmaxErrors=0` without `-o`; `python3 -I`; one Lean process of this job at a time.
- The 20 R2 modules: the 11 new modules, the changed `Combinators`, `FormulaArith`, `CircuitComplexity`,
  `ComputationalModels`, `TCSlib`, and the downstream `TreeNCAC`, `NCAC`, `Parity`, `Hierarchy`.
- Phase 2 on #4 also ran the full controls (strict and coe ALL_OK), the delivery's 30 controls (30/30), the unfold scan of
  the 16 files (167 items; 0 foreign in the 13 new files; only `TreeNCAC`'s 4), decls2 (267/0/0) and the clash scan.

## Known dispositions and slips (not findings)

- **Disclosed items** (review G6A-F04, F06, F08, F11, F14, F15 and the others): see question F. F01 is closed by LE-ren,
  F02 ruled (Q2 A), F03 ruled (Q3 A, out of scope), F05 pre-existing.
- **`review.md`'s final verdict names the snapshot-#4 heads** `a57dcf77`/`66036926` and adoption trees `ba964762`/
  `34e41f15`; the re-cut heads `a616adca`/`73aedcda` and trees `a461632b`/`2c243bb1` are in `phase2.md` § *Re-replay on
  snapshot #5*, the decision-log row "GSW 6a re-cut and re-replayed on snapshot #5" and the PR descriptions. `review.md`
  was not amended after the re-cut. Found at staging.
- **"Five definitions"**: the #359 description ("`sorryAx` is in exactly the 98 targets and five definitions") and the
  decision-log row "GSW 6a phase 2" ("98 targets plus 5 definitions") call the five dependents definitions; two are
  definitions (`toNANDForm`, `layerNAND`) and three are theorems (`toNANDForm_eq`, `layerNAND_gates`, `layerNAND_output`).
  `phase2.md` ("5 dependents") and `review.md` phase 1 name them correctly. The #359 description's "Every definition and
  reader is proved" is true of the source (no `sorry` token outside the 98 targets). Found at staging.
- **"20 owners"**: the decision log's "canonical coe-A re-run on all 20 owners" counts owner records over R1 and R2; there
  are 16 distinct owners (the 4 O1 owners are among the 16).
- **Range-diff wording**: the #359 description's "5/5 identical to the delivered series" compares with the worker's
  commits; `phase2.md` S5-1's "6/6 `=`" compares the re-cut with the snapshot-#4 landing branch (5 picks and LE-ren).
  Both hold.
- **Snapshot numbering**: `phase2.md` P2-8.1 says "adopt `olean-replay-6a-o1` as snapshot #5"; #5 is now the #340/#346
  snapshot, so a 6a adoption would be the next number, which Gate 48's pack also claims for `olean-replay-bb1sim`.
  Whichever merges first takes it; the other re-replays (§ *Merge interaction*).
- **decls2 for #358 alone** was run at checkpoint 1 against the issue base `f6f295a6` (7/0/0), not against `e1d39836`;
  #358's two pre-existing files are blob-equal at both bases and its four files are blob-equal to the worker's
  (`checks/blobs.txt`). The re-cut ran decls2 only tip → statement head (267 = 7 + 260).
- **Re-replay TOOLS.txt**: 8 of its 26 rows carry no `p2zip-match` annotation (the five archived Gate 10 tools, the
  phase-1 `names.py` and the two axiom probe sources); each matches a copy in the phase-1 or phase-2 ZIP by SHA-256
  (`checks/tools-carry.txt`). Found at staging.
- **About 360 MB of raw records** (seal records, control sources, probe logs, state files, name lists, full state checks) are not copied into
  `verification-r1.zip`; they are inside the three recorded evidence ZIPs, whose manifests are copied
  (`SHA256SUMS.original`) and whose own SHA-256 are in `POINTERS.md` and `records/…/final-6a-r1/evidence-SHA256SUMS`.
- **No Lean, no `lake`, no seal or control was run for this pack.** `phase1/`, `phase2/` and `rereplay5/` are the reviews'
  recorded evidence; `checks/` are git-object reads and hashes at staging.
- **Authorship.** The six worker commits were written by an external Claude worker (a lead with two sub-agents: `bp` for
  BranchingPrograms, `fa` for FormulaArith), delivered as patches (exchange `d7a9adb5`, unsigned), reproduced by
  `git am`, and cherry-picked and signed by the maintainer; LE-ren is the maintainer's. The signing key is shared by the
  account's Claude sessions (rule 9 above).
- **The PR descriptions** (`pr358-description.md`, `pr359-description.md`) are the REST `.body` values at staging
  (#358 updated 2026-11-17T09:46:54Z, #359 09:47:21Z).
- **Bundle.** `bundle.md` is on the exchange only, not in the records (`workflow.md` §3).

## Merge interaction (maintainer merge conditions, not audit items)

`checks/mergetrees.txt` (`git merge-tree --write-tree`, git 2.43.0; import overlap from the `import TCSlib.*` lines of each
merged tree):

| Other side × #359 head `73aedcda` | Merge base | Result | Shared paths | Modules downstream of both |
|---|---|---|---|---|
| records pin `8c5875fa` | `e1d39836` | clean, tree `ab4aff19…` | none | — |
| **#357** `land/pairings-bb1-sim` `7a98ba01` | `e1d39836` | clean, tree `a8941d86…` | none | `TCSlib` only |
| **#347** `cleanup/dw5-derand-readers` `daa6e173` | `2da7e0f3` | clean, tree `a09d46bc…` | none | `TCSlib`, `CircuitComplexity` |
| **#355** `land/cleanup-stage1` `d3c7cb00` | `2da7e0f3` | clean, tree `dffff2bf…` | none of the 18 series paths¹ | `TCSlib`, `CircuitComplexity`, `ComputationalModels` |

¹ `TCSlib/Cryptography/Games.lean` is changed on both sides since the old merge base `2da7e0f3`, through the records
history (#351's import, already on the tip); #359 does not touch it. Each merge with #358's head is clean too.

- **No shared path** with any of the three: neither #357, #347 nor #355 touches one of the 18 series paths, and none of
  their modules is in the import closure of a non-aggregate 6a module.
- **Import overlap and snapshot adoption.** The 6a replays (`olean-replay-6a-o1`, `olean-replay-6a-stmt`) are adoptable
  only if the merge commit's Lean paths equal tree `a461632b` (then `2c243bb1`), i.e. #358 and #359 merge next, in that
  order, with no other code PR between. If **any** of #357, #347, #355 merges first, the Lean paths differ and the 6a PRs
  re-replay (9 and 20 modules; the 6a downstream set does not grow). Conversely, a 6a merge voids the others' replay
  outputs: with **#357** only through the import-only root (as for #340/#346); with **#347** also through the
  `CircuitComplexity` facade, and with **#355** through `CircuitComplexity` and `ComputationalModels`, both of which 6a
  changes and which lie downstream of those PRs' modules. So neither side's adoption survives the other's merge; the
  re-replays are independent apart from those aggregate modules.
- **Order:** #358 first, then #359 retargeted to `cryptography/pass-shelat-ch2-4`. Merge conditions: Gate 45 closed (zero
  blockers and zero majors) and the snapshot adoption check above.

## Evidence files

- **`pack-r1.md`** (this file), **`dispatch-r1.md`** (the Codex prompt; records only).
- **`pr358.diff.txt`**: `git diff e1d39836..a616adca` (4 files, +279/−184; SHA-256
  `f247ec4d09f171557c99e724871e3ca2dbbb1b8488faada234b95c0a243555fb`); **`pr359.diff.txt`**: `git diff a616adca..73aedcda`
  (17 files, +3383/−2; SHA-256 `ec8fd096289396075fa25ff90c176ae8ba7578e3bcc31a35aaeb4f8c9e9a8823`). Each equals its
  three-dot view byte for byte.
- **`pr358-description.md`**, **`pr359-description.md`**: the PR bodies at staging (REST `.body`, raw).
- **`source-head-r1.json`**: the pins, both PRs' commits (parent, tree, author, committer, gpgsig presence, files), and for
  each changed file its status, blob, SHA-256, line counts at base and head, maximum width, over-width, tabs and trailing
  spaces.
- **`sources-r1.zip`**: `head-73aedcda/` the 17 Lean series files; `o1-a616adca/` #358's four files; `base-e1d39836/` the
  series Lean files that exist at the base; `context-73aedcda/` the unchanged modules the new files import or cite
  (`Basic`, `TreeDAG`, `DAGCircuit`, `DAGTransform`, `DAGFanin`, `Adder`, `NCAC`, `Hierarchy`, `Parity`, `LayeredDAG`,
  `LMN/CircuitReindex`); `references/` the Bar89, BV14 and BV11 ingests (`.md`, `.raw.md`). Its `README.md` gives every
  entry's SHA-256 and origin.
- **`verification-r1.zip`**: `MANIFEST.md`, `POINTERS.md` and `SHA256SUMS` (every other entry).
  - `checks/`: the staging's git-object checks (`series`, `blobs`, `le-ren`, `targets`, `sorryax-dependents`, `tags`,
    `sizes`, `mergetrees`, `tools-carry`) and their scripts;
  - `phase1/`: the phase-1 review evidence ZIP, whole;
  - `phase2/`, `rereplay5/`: the phase-2 and re-replay evidence ZIPs' summary files (each with its full manifest as
    `SHA256SUMS.original`; `sha256sum -c --ignore-missing`);
  - `delivery/`: from the exchange delivery `d7a9adb5`: `REPORT.md`, `COMMITS.tsv`, `rowmap.txt`,
    `targets-per-module.tsv`, `definitions-readers.txt`, `quotes-check.txt`, `AxiomProbe.lean`/`.log`, the frozen-file
    check and its controls, the probe summary, and the 30 paired controls (`.lean` and `.log.summary`); the delivery's two
    manifests are named by SHA-256 in `POINTERS.md`, and its `decls2.tsv` equals `phase1/statements/decls2.tsv`;
  - `records/`: plan r3, the rulings and questions, the checkpoint-1 review, `review.md`, `phase2.md`, the evidence sums,
    the issued package (README, brief, dispatch, addendum, sums, base sorries), Gate 44's findings, `policy.md`,
    `workflow.md`, the decision-log rows from 2026-11-16 on, and ledger row DL-54;
  - `pr/`: the two PRs' REST fields at staging.
- **`SHA256SUMS-r1`**: the files of this gate directory.

## Findings delivery

Return `gate45-gsw-6a-findings.md` as Markdown in this chat. If you have several evidence files, return a ZIP.

| # | Severity | PR · file · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Number the findings **G45-01, G45-02, …**. Grade G6A-F01 to G6A-F15 in a separate table (agree, or regrade with the
reason). Report the audited heads, the records pin, the counts by severity per PR, and one verdict per PR and overall:
**CLEAR** (zero blockers and zero majors) or **HOLD**. The gate closes at zero blockers and zero majors.

**Severities** (`workflow.md` §3)
- **blocker:** a downstream phase (the 6a fills or 6b) would build on a wrong statement: a false, vacuous or unusable
  target or definition, a target too weak for its planned consumer, a proof in #358 that does not establish its
  statement, or a scope violation.
- **major:** fixable but materially misleading: a changed `TreeNCAC` statement; a mis-stated source correspondence or a
  fabricated tag or locator; an undisclosed (or unaccepted) duplicate of a public lemma; a forbidden read in #358 not
  covered by the rulings; a definition that depends on an admitted target beyond a proof field; necessary evidence that
  cannot be verified (including a carry-forward claim that does not hold).
- **minor:** documentation or API defects: an inaccurate formula docstring, deviation note, glue note, proof sketch or
  citation; a missing reader.
- **note:** anything else.
