# External audit pack — Chapter-6 circuit surface (proved material)

Audits commit `28690c01` on `complexity/arora-barak-ch1`. This is the
**first proved-material audit of the campaign**: the chapter-6 circuit
tree merged from `complexity/arora-barak-ch6` (authors: Yichuan Wang,
Hydroxyi), **fully proved — zero sorries in scope** — which the campaign
must attest before any campaign statement cites it (`backlog.md` §4). The
audit protocol is the statement-phase protocol of `workflow.md` §3 with
one inversion, stated under *Brief*: the proofs are kernel-checked, so the
only thing that can be wrong is **what the definitions mean**. The product
under audit is definitions, theorem statements, conventions, and the
completeness of the files' own divergence ledgers — not proofs. The gate
closes on zero blockers/majors. Record findings in
`audits/ch6-circuits-findings.md`.

Source texts: [AB09] §6.1–6.2 (Defs 6.1–6.5, Example 6.3, Claim 6.8 and
the surrounding remarks, Defs 6.9–6.14, Lemma 6.11, p. 112's concrete
representation), §6.5 (Thm 6.21, Thm 6.22), §6.7.1 (Defs 6.24–6.25);
[OD14] §3.2 and §4 for the tree-circuit substrate `Basic.lean` inherits
from the switching development. Where this pack asserts an [AB09] item
number, checking that assertion is part of the audit: a wrong mapping is
itself a finding (minor, unless it conceals a divergence).

## Scope

In scope — 13 content modules plus the facade, attached in full:

`TCSlib/Complexity/CircuitComplexity.lean` (facade), and under
`TCSlib/Complexity/CircuitComplexity/`: `Basic`, `CircuitSat`, `Encoding`,
`FeedForward`, `HardFunctions`, `Hierarchy`, `NCAC`, `PPoly`, `Parity`,
`SizeClasses`, `UHalt`, `UnaryLanguages`, `Universal`.

Out of scope, deliberately: `Formulas.lean` (OD14 switching
infrastructure, not AB09 chapter-6 surface; under concurrent rework);
`BooleanAnalysis/DecisionTree.lean` and the Switching/LMN trees (the OD14
track); the `RazborovSmolensky` chain (not yet cited by any campaign
statement; interface-only audit when one does); all closed campaign gates
(Chapter 1, Chapter 2 phases 1–4 — trusted context). The catalog facade
`TCSlib/ComputationalModels.lean` and the sweep list
`scripts/circuit_module_order.txt` are attached for orientation, not for
audit.

## Rename disclosure (this month's nomenclature passes)

The attached files are post-rename; any cross-reference you reconstruct
from older material maps as follows. `HasLogDepth` → `HasPolylogDepth`.
The `ACP` namespace was unbundled: the `FeedForward` model, `CircuitFamily`,
`PPoly`, and the tree-model files now live in `BoolCircuit`; the
Razborov–Smolensky chain in `RazborovSmolensky`; `AC_GateOps` →
`BoolCircuit.stdGateOps`. `FeedForwardCircuit.lean` was relocated to
`CircuitComplexity/FeedForward.lean` (gaining `stdGateOps`), and
`DecisionTree.lean` to `BooleanAnalysis/` (gaining
`DecisionTree.buildFull`). `SwitchingLemma2` → `SwitchingLemma` (out of
scope here). No statement changed under any rename; each pass was
verified by full dependency sweeps recorded in the commits
(`88e15478`, `4046e553`, `9ab1a241`, `193470a3`, `1f6e71d9`).

## Repository-side attestations (maintainer, local machine — verify or challenge)

1. **Freeze.** Commit `28690c01`. Zero `sorry` in the 14 attached files;
   all 59 campaign admissions live outside this scope, byte-identical
   with their closed gates. ~258 public declarations in scope.
2. **Elaboration.** Fresh-olean sweeps via `scripts/lean_check_tree.sh`,
   Lean 4.25.0 / mathlib `029db123ddaa`: the 23-module circuit list
   (`scripts/circuit_module_order.txt`) and a 39-module batch covering
   the Switching/LMN reverse dependencies, both zero `error:` lines, at
   this commit's lineage. A pre-merge-state baseline sweep passed before
   the rename passes began, so compilation is attested on both sides of
   every rename.
3. **Axiom prints.** 30 headline theorems spanning every in-scope file
   plus `RazborovSmolensky.MODq_notin_AC0p_quantitative`: each depends on
   exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx`
   (kernel-level sorry-freedom), no `Lean.ofReduceBool` — and a
   repo-grep confirms no `native_decide` anywhere in the two trees.
4. **Policy.** Style lint: 0 FAIL / 0 WARN over the `CircuitComplexity/`
   directory. Blueprint label validation: 0 orphan `\lean` labels after
   the generated artifacts were healed.
5. **Provenance.** The material is main-track work by the chapter-6
   authors, merged at `a2a2728b`; it was **not** produced under the
   campaign's sketch-first discipline, which is why this audit exists.
   The campaign's own two statements of contact (`Theorem 6.6`,
   CKT-SAT `NP`-hardness) are *future* statements, deferred in
   `backlog.md` §3; nothing in scope claims them.

## What is under audit

| Module | Key definitions | Headline statements | Anchor; declared divergences |
|---|---|---|---|
| `Basic` | `Lit`, `Circuit` (tree; unbounded fan-in; polarity on leaves; no NOT/const nodes), `NAndCircuit`/`NOrCircuit`, `toNAnd`/`toNOr` | semantics lemmas; `one_le_size`; normalization preserves `eval`/`litCount`, ≤2× size | [OD14 §4.5]; tree not DAG; `size` counts leaves; no width measure |
| `CircuitSat` | `CktVar`, `Circuit.tseitin`, `Circuit.toCNF` (into legacy `NPReductions.CNFFormula`), `tseitinAssignment` | `satisfiable_iff_isSatisfiable`, `mem_cktSat_iff_is3Satisfiable`, `tseitin_length_lt`, `toCNF_length_le` (≤ 3·size) | [AB09 Lem 6.11] — **equisatisfiability only, no ≤p**; output variable type infinite, no output-encoding bound |
| `Encoding` | `encodeCircuit`/`readCircuit` (unary indices, tag bits), `encodeSigma`/`decodeSigma`, `circuitEncoding : FinEncoding`, `cktSatLang` | round-trips; `size_le_length_encodeSigma`; `length_to3SAT_toCNF_le` (≤ 13·length 3-clauses) | [AB09 Def 6.9, p. 112]; tree encoding replaces the adjacency matrix; unary inflation upward-only; non-canonical strings decode to `none`, absent from `cktSatLang` |
| `FeedForward` | `GateOp`, `Gate`, `FeedForward` (layered DAG, any alphabet), `stdGateOps` ({id, NOT, unbounded AND}), `IsAndOrGate` | `toCircuit`/`toFeedForward` conversions with eval-preservation and size bounds ((k+1)^depth up; size·(depth+1) back) | model infrastructure under [AB09 Def 6.1]; layering and node-counting conventions declared in `PPoly.lean` |
| `HardFunctions` | (counting helpers) | `encodeCircuit_injective`, `card_computable_le` (≤ 2^((n+4)·S)), `exists_hard_function` | [AB09 Thm 6.21]; counting via the tree encoding, not AB's |
| `Hierarchy` | `widenCircuit`/`restrictCircuit`/`onFirst`, `Language.InTreeSize`, `TreeSize`, `padFamily`/`padLanguage` | `treeSize_ssubset`, `treeSize_ssubset_of_lt`, `treeSize_one_ssubset`, `zero_mem_treeSize_one` | **variant of** [AB09 Thm 6.22] over `TreeSize`, explicitly *not* that theorem (no gate-set restriction; tree size classes) |
| `NCAC` | `TreeCircuitFamily` with `IsPolySize`/`HasFaninTwo`/`HasPolylogDepth`, `Language.InNC`/`InAC`, `NCLevel`/`ACLevel`, `NC`, `AC` | fan-in simulation `InAC.inNC_succ`; `NC_eq_AC` (true for the unions; reader-surprising) | [AB09 Defs 6.24–6.25]; `(log n + 1)^d` repairs log-degeneracy; `NC` takes i ≥ 1, `AC` takes all i |
| `PPoly` | `CircuitFamily` (`finite` built in), `OnlyUsesGates`, `IsPolySize`, `Language.InSIZE`/`InPPoly`, `PPoly` | `inPPoly_iff` | [AB09 Defs 6.1/6.2/6.5]; unbounded-fan-in `stdGateOps` vs AB's fan-in 2; `(n+1)^k` vs `n^c` degeneracy repair; `Nat.card` trap documented; **circuit-family definition only** (no TM-with-advice characterization) |
| `Parity` | `parityCircuit` | `parityCircuit_size_le` (≤ 32·(n+1)^4), `mem_parity_iff`, `parity_inNC_one` | [AB09 §6.7.1 example] |
| `SizeClasses` | `Language.allOnes`, `andGateOp`, `allOnesCircuit`/`allOnesFamily` | `InSIZE.mono`, `InSIZE.inPPoly`, `allOnes_inSIZE_one`, `allOnes_inPPoly` | [AB09 Ex 6.3]; Thm 6.6 deferral note points at `backlog.md` §3 |
| `UHalt` | `Nat.Partrec.Code.haltingSet`, `Language.uhalt` (unary, Gödel-numbered via `unpair`) | `uhalt_inPPoly`, `not_computablePred_mem_uhalt`, `exists_le_allOnes_inPPoly_not_computablePred` | [AB09 §6.1.1, undecidable-languages-in-P/poly remark]; undecidability is Mathlib's `ComputablePred.halting_problem` transported, a **second computability framework** relative to the campaign's machines |
| `UnaryLanguages` | `notGateOp`, `constZeroCircuit`, `unaryFamily` | `unaryFamily_language`, `inSIZE_two_of_le_allOnes`, `inPPoly_of_le_allOnes`, `unary_inPPoly` | [AB09 Claim 6.8] |
| `Universal` | `minterm`, `universalCircuit` (OR of minterms) | `universalCircuit_eval`, `universalCircuit_size_le` (≤ 2^n·(n+1)+1, attained), `exists_circuit_eval_eq_size_le` | [AB09 §6.1]'s trivial exponential upper bound; the O(2^n/n) refinement is **not** formalized |

## Brief for the auditor

Ground rules: every proof in scope is kernel-checked under the axiom
prints above — **do not audit proofs**; a proof is relevant only when a
definition's meaning is pinned by a round-trip or characterization lemma.
Closed campaign gates are trusted context. The files carry unusually
thorough docstrings with their own `## Divergences` sections; those
ledgers are themselves objects under audit. Priorities:

1. **Blind restatement.** For each of [AB09] Defs 6.1, 6.2, 6.5, 6.9,
   6.24, 6.25, and the statements of Claim 6.8, Thm 6.21, Thm 6.22:
   restate the item from the book, then diff against the Lean. Return a
   per-item verdict table (faithful / faithful-with-declared-divergence /
   divergent-undeclared / not-the-claimed-item).
2. **Definitional attack pass.** The phase-1 lesson transfers: a true
   theorem about a wrong definition is the failure mode. Seeded attack
   surfaces, to be executed and extended:
   - *Gate smuggling.* `GateOp` admits any function as one gate. Verify
     every class in scope either restricts the basis
     (`OnlyUsesGates stdGateOps`) or is structurally restricted (tree
     `Circuit` nodes are AND/OR over literals). `TreeSize` deliberately
     has no basis restriction — check that is benign and declared.
   - *Finiteness/`Nat.card`.* `FeedForward.size` returns 0 on an
     infinite layer. `CircuitFamily.finite` is the declared guard; check
     no route into `InSIZE`/`InPPoly` evades it.
   - *Malformed strings.* `cktSatLang` membership for non-canonical
     words: the declared convention is decode-to-`none`, hence absent.
     Verify both directions; this is the recurring enumerator lesson.
   - *Quantitative conventions.* Unary-index inflation must only ever
     weaken upper bounds; `(n+1)`-style repairs must not change the
     classes; check the 2^((n+4)·S), 3·size, 13·length, 32·(n+1)^4,
     2^n·(n+1)+1 constants against the constructions they count.
   - *Degeneracies.* n = 0 circuits, the empty word (ε ∈ `allOnes`?,
     `parityCircuit 0`), `HasPolylogDepth 0` (= constant depth, used by
     `AC⁰`), `NC`'s i ≥ 1 versus `AC`'s unrestricted union,
     `zero_mem_treeSize_one`'s empty-OR convention.
   - *Boundary conversions.* `finTwoEquiv` at the `Fin 2`/`Bool` seam:
     one orientation (`1` ↔ `true`) used consistently in `Accepts`,
     `language`, and the gate semantics.
   - *Class-equality conventions.* `C.language = L` (set equality)
     versus pointwise-iff membership — check nothing weakens a class by
     quantifier placement.
3. **Divergence-ledger completeness.** The declared divergences are in
   the table above. The finding class that matters: a divergence that is
   *real but unflagged*. Hunt especially where AB09 makes a choice the
   files are silent about.
4. **Statement-versus-prose.** Docstrings, the facade's `## Contents`,
   and the catalog's one-liners must say what the formal statements say
   (`NC_eq_AC` is true for the union classes — flag places where prose
   would mislead a reader into thinking a false strengthening holds).
5. **Interface preview (advisory, not gating).** The campaign's next
   statements will be `P ⊆ P/poly` and CKT-SAT `NP`-hardness over this
   surface plus the campaign machines. Flag anything in the definitions
   that would make those statements awkward or wrong to state — advisory
   findings, severity *note*.

Severity scheme as always: **blocker** (a definition does not mean what
it must), **major** (a statement or ledger materially misleads; a
quantitative claim wrong), **minor** (prose, naming, mapping errors),
**note** (advisory). Findings to `audits/ch6-circuits-findings.md`, one
numbered finding per item with file:line and a proposed repair; the
verdict table from task 1 included. This pack is immutable once sent;
errata, if any, will be acknowledged in the resolutions file.
