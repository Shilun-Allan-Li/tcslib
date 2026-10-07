# Chapter-6 circuit surface — audit loop resolutions (CLOSED, 2026-10-02)

Protocol: `workflow.md` §3. Three rounds. Round 1: pack
`audits/ch6-circuits-pack.md` (commit `05971a42`, auditing `28690c01`),
findings `audits/ch6-circuits-findings.md` — 0 blockers, 4 majors,
7 minors, 4 notes. Round 2: pack `audits/ch6-circuits-reaudit-pack.md`
(commit `4eefb77c`, auditing `12ff3add`), findings
`audits/ch6-circuits-reaudit-findings.md` — 0 blockers, 3 majors,
3 minors. Round 3: pack `audits/ch6-circuits-round3-pack.md` (commit
`39512aad`, auditing `3ff0d76b`), findings
`audits/ch6-circuits-round3-findings.md` — **0 blockers, 0 majors,
2 minors: the gate closes** under the zero-blocker/major rule, with the
two round-3 minors swept in the closing commit per standing practice.
Every finding across all rounds was accepted after source verification;
none was contested. All repairs were documentation only — **zero Lean
statements changed in the entire loop**. Packs and findings files are
immutable/verbatim; this file is the living record.

## Round-1 repairs (findings 1–11)

*(Table as recorded before round 2; see errata R-E1 below for the two
historical corrections round 2 and round 3 forced.)*

| # | Sev. | Repair |
|---|---|---|
| 1 | major | `FeedForward.lean`: `Circuit.toFeedForward` re-described as a **semantic wrapper** (single unrestricted `⟨Fin n, C.eval⟩` gate + identity wires; `size = depth = C.depth + 1`; never discharges `OnlyUsesGates`; only evaluation preserved) in the declaration docstring, the module docstring, and the section header; the false `C.size * C.depth` prose bound removed. Catalog entry rewritten to match. `Hierarchy.lean`'s already-accurate disclosure untouched. |
| 2 | major | `Basic.lean`: divergence ledger rewritten — the normal forms are *alternating trees over base clauses*, not [OD14, Def 4.26]'s layered circuits (no common input layer, unequal literal paths); the three size/depth measures declared non-interchangeable with the clause-of-two-literals example, the root-counting convention, and the `.node []`/`.clause []` depth asymmetry; the mutual-block header de-attributed from Def 4.26. |
| 3 | major | `PPoly.lean`: "All are class-preserving" restricted to the polynomial union, with the `allOnes ∈ InSIZE (fun _ => 1)` counterexample recorded; `InSIZE` labeled as this model's size class. `Hierarchy.lean` and the facade weakened from identification to rendering-with-divergences. |
| 4 | major | `HardFunctions.lean`: the "strictly the stronger" comparison replaced by the neither-implication statement with the n = 20 instance (5242 → 5202 ≪ 41943); facade reads "tree-circuit analogue of [AB09, Thm 6.21] … no **tree** circuit". |
| 5 | minor | Graph/nullary conventions collected (`PPoly.lean` ledger; `Basic.lean` empty AND/OR conventions; `UnaryLanguages.lean` constant-operation wording; catalog basis-optionality). |
| 6 | minor | "Forced representation" claims corrected to "unimplemented, not impossible" (`CircuitSat.lean`, `Encoding.lean`). |
| 7 | minor | Stale "no machine model / no `P`" corrected at the three sites round 1 found (`CircuitSat.lean`, `Encoding.lean`, facade `UHalt` bullet). |
| 8 | minor | Exact-value narration of upper bounds corrected (`UnaryLanguages.lean` ledger; `Parity.lean` ledger and `xorFuel_depth` docstring). |
| 9 | minor | `NCAC.lean`: `NC_eq_AC` docstring says the **unions** coincide. |
| 10 | minor | Length-3 attribution and the Exercise 6.1 label fixed; pack-side source-map errors acknowledged (erratum P-E1 below). |
| 11 | minor | Sweep-list count discrepancy acknowledged (erratum P-E2 below). |

Notes 12–15 were recorded as inherited interface guidance in
`backlog.md` §3 (gate-by-gate family construction against
`OnlyUsesGates stdGateOps`; the CKT-SAT route from the audited
`Std.Sat.CNF ℕ` carrier with a total string map and fixed rejecting
word; dense variable renumbering before unary indices; the
campaign-decidability → `ComputablePred` bridge). Round 2 confirmed the
recordings; no implementation obligation attached.

## Round-2 repairs (findings R2-1 … R2-6)

Round-1 major 2 and minors 5–7/9–10 were discharged in round 2; the
Def 6.1 / Def 6.2 verdicts were upgraded to
*faithful-with-declared-divergence*. The three round-2 majors were
survivals of round-1 claims at sites the first pass missed.

| # | Sev. | Repair (commit `3ff0d76b`) |
|---|---|---|
| R2-1 | major | `FeedForward.lean`: the mid-file conversion overview — the fifth description site — rewritten to the wrapper account (no faithful embedding, no `C.size * C.depth` bound); the surviving "embedded/embedding" docstrings reworded; the depth docstring attributes the `+ 1` to the evaluation layer. Round 3 confirmed discharge. |
| R2-2 | major | `Hierarchy.lean`: the Main-results bullet stops identifying the book theorem's class with `Language.InSIZE`; `PPoly.lean`: the fan-in sentence restricted to polynomial-size existence. Round 3 confirmed discharge. |
| R2-3 | major | `HardFunctions.lean`: the surviving "weaker statement" conclusion replaced with the neither-implication account; the "never rules out" sharing warning rephrased as no-transfer-at-these-cutoffs. Round 3 confirmed discharge. |
| R2-4 | minor | `Parity.lean` proof sketch and `UnaryLanguages.lean` Claim-6.8 docstring say "at most". Round 3 confirmed discharge. |
| R2-5 | minor | "Can never discharge `OnlyUsesGates`" / "never a gate basis" corrected to "no general basis guarantee" (declaration docstring, catalog, `backlog.md` §3), with the `andGateOp 1` counterexample noted; `Hierarchy.lean`'s image-size rationale replaced by the true obstruction (`C.depth ≤ C.size`, so the wrapper's size is `≤ C.size + 1`; the missing basis proof is what blocks transport). One unqualified clause survived — round-3 finding R3-2, swept below. |
| R2-6 | minor | Verification appendix and raw logs supplied — but the committed resolutions file was stale (erratum R-E3 below); the appendix as corrected by the round-3 auditor's independent reconstruction appears below. |

## Round-3 repairs (findings R3-1, R3-2 — swept in the closing commit)

| # | Sev. | Repair |
|---|---|---|
| R3-1 | minor | **This file.** The round-3 bundle's resolutions attachment lacked the promised round-2 table, appendix, and errata: the maintainer's editing script replaced text without occurrence assertions and a wording mismatch made the edit a silent no-op, so a stale 61-line file was committed and attested as updated (erratum R-E3). The full record — with the appendix corrected against the round-3 findings' §3 reconstruction, including run B's actual manifest — is this version. |
| R3-2 | minor | `Hierarchy.lean`: "one gate … that is not in `stdGateOps`" qualified to "an unrestricted gate that, even after alphabet transport, need not belong to `stdGateOps`"; the `FeedForward.lean` docstring example now names `C : Circuit 1`. |

## Errata (sent packs and this file's own history; packs immutable)

* **P-E1 (round-1 pack).** Theorem 6.22 is in **§6.6** of the published
  2009 edition, not §6.5; the quoted ranges "Defs 6.1–6.5" and
  "Defs 6.9–6.14" mix definitions with examples, a lemma, and a theorem —
  read as section ranges.
* **P-E2 (round-1 pack).** "The 23-module circuit list": the attached
  `scripts/circuit_module_order.txt` has **22** entries; the count was
  stale after `DecisionTree`'s relocation (commit `193470a3`) removed its
  line shortly before the pack was written.
* **R-E1 (this file, round-1 table).** Row 1 claimed the false
  `C.size * C.depth` bound was "removed" and endorsed `Hierarchy.lean` as
  untouched-and-accurate: the bound in fact survived in the file's
  conversion overview until the round-2 repairs, and `Hierarchy.lean`'s
  rationale contained the image-size overstatement corrected under R2-5.
  The row's own "never discharges `OnlyUsesGates`" phrasing is likewise
  superseded by R2-5. The row is preserved as written (it was audited in
  that form); this erratum is the correction of record.
* **R-E2 (round-2 pack).** Attestation 2 wrote "31 Switching/LMN
  reverse-dependency modules"; the correct segment count is **32**, so
  the total is `22 + 32 + 1 = 55`, matching the log. Verified
  independently by the round-3 auditor.
* **R-E3 (round-3 bundle).** The attached resolutions file was stale
  (see R3-1). The round-3 pack's descriptions of its intended contents
  were accurate about intent but wrong about the attachment; the
  auditor's §3 reconstruction stands as the independent verification of
  the appendix's arithmetic.

## Verification appendix (runs of record; logs in `audits/logs/`)

All runs via `scripts/lean_check_tree.sh` (fresh-olean gate), Lean 4.25.0
/ mathlib `029db123ddaa`. Module sequences verified against the two
order lists by the round-3 auditor (findings §3): ordered equality holds
as stated below, no duplicate markers, zero `error:` lines in all four.

| Run | State | Manifest (verified) | Count | Log |
|---|---|---|---|---|
| A | merged pre-rename state (before `88e15478`) | the then-current circuit list: today's 22 entries minus `CircuitComplexity/FeedForward`, plus the old `RazborovSmolensky/FeedForwardCircuit` and `CircuitComplexity/DecisionTree` paths | 23 | `ch6-baseline-sweep-premerge-state.log` |
| B | `193470a3` worktree | switching list lines 3–34 (32), then six circuit modules (`SizeClasses`, `UnaryLanguages`, `UHalt`, `NCAC`, `Parity`, the facade), then the catalog | 39 | `ch6-batch-sweep-39mod-193470a3.log` |
| C | `12ff3add` | the full circuit list (22), then switching list lines 3–34 (32) — disjoint from the first segment, which contains the overlap entries `Basic`/`Formulas` — then the catalog | 55 | `ch6-repair-sweep-55mod-12ff3add.log` |
| D | `3ff0d76b` | circuit list lines 4–22 (19, from `FeedForward` onward), then the catalog; the Switching/LMN trees import none of the six edited files | 20 | `ch6-round3-sweep-20mod.log` |
| E | gate-closure commit (R3-2 touches `FeedForward.lean`, `Hierarchy.lean`) | same manifest as run D | 20 | `ch6-close-sweep-20mod.log` |

Two observations from the logs, recorded for completeness (round-3
findings §3): runs B and C each show five `declaration uses 'sorry'`
warnings in four **LMN** files (`CircuitCompression`,
`IterativeReduction`, `Depth3Switching` ×2, `CircuitTreeManip`) — outside
this audit's scope, but the LMN tree is therefore **not** sorry-free,
unlike the circuit and Razborov–Smolensky trees; and "zero `error:`
lines" is not "warning-free" for those two runs.

## Closure

Gate **CLOSED** 2026-10-02 at the closing commit, round 3 reporting
0 blockers / 0 majors, with R3-1 and R3-2 swept in that commit. What
closure attests: the 13 content modules and facade of
`Complexity/CircuitComplexity/` carry externally audited definitions and
theorem statements — verdicts *faithful* (Claim 6.8) or
*faithful-with-declared-divergence* (Defs 6.1, 6.2, 6.5, 6.9, 6.24,
6.25; Thm 6.21) against [AB09], with the Thm 6.22 analogue explicitly
unclaimed — over kernel-checked proofs with the standard axiom triple.
Campaign statements may now cite this surface, subject to the recorded
divergences and the four inherited interface notes in `backlog.md` §3.
What closure does **not** attest: equivalence of the tree classes with
the book's DAG classes, the book's Thm 6.21/6.22 themselves, any
polynomial-time reduction, or anything about `Formulas.lean` (excluded,
under concurrent rework) or the Switching/LMN/RazborovSmolensky trees.
