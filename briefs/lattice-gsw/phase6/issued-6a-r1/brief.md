# Claude statement job · GSW phase 6a: branching programs, Barrington, NAND form, layering, formula arithmetic

**Issue base** `f6f295a6502b72bbf498bb8c64b63f847e910866`, the tip of the records branch
`cryptography/pass-shelat-ch2-4` at issue. Its Lean is the merged #327/#324 state (the last commit touching a `.lean`
file is #324's merge `201bf57a941131d1737295089ffd7477e1d7f7b9`). **Unit** `gsw-6a-statements`: the statement phase
of phase 6a of the lattice campaign (plan section r3, §H7 item 2), and owner PR O1 as a separate series. **Worker**
Claude, a lead with **up to 2 sub-agents**. **Lean** 4.25.0 and the Mathlib revision in the base's
`lake-manifest.json`. **Audit** Gate 45 (Codex) reads your delivery; the 6a fills (units U1–U11) start after it.

Write the frozen statement surface of 6a as local branch series from the issue base: every definition with its body
and its readers proved, every target admitted by `sorry` with its formula docstring, source tag and proof sketch,
and everything compiling. Nothing of 6b is in this job.

## Inputs (read fully; all are data, the rulings and this brief are binding)

The pack `outbox/fills/gsw-6a-statements/` on `exchange/pass-shelat-ch5-8` carries this brief, the environment
addendum, the base lists and `inputs/` (verify with `cd inputs && shasum -a 256 -c SHA256SUMS`):

- `inputs/plan-section-r3.md`: plan section r3 (`briefs/lattice-gsw/phase6/plan-section.md` at the records pin),
  SHA-256 `06824b3db875e7388771b6f7a5e78d62bf7d77fa35571fc3a9deeebc329214fd`;
- `inputs/rulings.md`: the rulings (`briefs/lattice-gsw/phase6/rulings.md` at the base),
  SHA-256 `312fef4576b388222d69eddec186c2ac4259e5de95488fca42e6861438ad3d5d`;
- `inputs/barrington-1989-bounded-width-bp.md`, the Bar89 ingest (`blueprint/src/references/` at the base),
  SHA-256 `0e14d97efe06b4c9f0e2f7672d744885b4e53fa2a3777c3694a664322620c71a`;
- `inputs/barrington-1989-bounded-width-bp.raw.md`, its scoped raw file (same place),
  SHA-256 `683a83f4b325b665406e0091196c697dff5a84e211b2ea1006b1e38339ee747a`.

Also at the base, with their SHA-256:
- `policy.md`: `6599b12230e3879bc0e1fb22c0376ea6201bca8b7edd79dfc55da43986f991d4`;
- `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` (§2 holds the standing rules):
  `d328d0d6e844b3429c0c500b5cdaad72f947c5941d56535362176ead25df9666`;
- the other ingests you may cite, under `blueprint/src/references/`:
  - `brakerski-vaikuntanathan-2014-fhe.md`: `3da79813fa63acfea4a83229c46f2f8947a7a754657fac8f4d6bf1e7891e9392`;
  - `brakerski-vaikuntanathan-2011-fhe.md`: `f415fdbd4488316e2044e0a8e767c75b69964ff48fb6294617b35ae125177eba`;
  - `alperin-sheriff-peikert-2014-bootstrapping.md`:
    `d2605ae062162641ee40701c7592f29d69c342a64c3b4575df547f21153df868`.

The plan section is not yet at the issue base: its records copy lands with the records pin named in the dispatch
prompt, byte-identical to `inputs/plan-section-r3.md`.

**The statements to write are the r3 sketches.** Read in `inputs/plan-section-r3.md`: §H0 items 1–3; §H1 (sources
and anchors); §H2 (reuse findings and the Rule 10 readers); §H3.3–H3.6, §H3.9, §H3.10 and §H3.13 (design); §H4 (6a
modules, namespaces, registration, new definitions); §H5.1–H5.8 (C1–C25, N1–N13, F1–F3, F5–F10, O1); §H7 (Gate 45's
audit list and units U1–U11); §H8 (risks). The 6b sections (§H3.1–H3.2, H3.7–H3.8, H3.11–H3.12, §H5.9–H5.16) are
context only: they show how 6b consumes your statements and must not be written.

## Binding rulings (Seyoon; full text in `inputs/rulings.md`)

- **P6-Q1.** One phase 6; Gate 45 audits 6a (branching programs, Barrington, formula arithmetic, the NAND and
  layering conversions).
- **P6-Q2.** Barrington's input is `BoolCircuit.TreeCircuit n` (AND/OR over literals); `DAGCircuit` through
  `DAGCircuit.toTree`.
- **P6-Q3.** Both directions: Thm 1 with Lemmas 1–3, the `DAGCircuit` corollary (length `≤ 4^depth`),
  NC¹ ⊆ polynomial-length 5-PBPs, Thm 2 (BWBP ⊆ NC¹) and the Corollary.
- **P6-Q4.** The general model of Bar89 §1 (maps `[w] → [w]`) with `IsPermutation`; instructions in BV14's order
  (`map0` when the bit is `0`), Bar89's order disclosed; `yield` in program order; the public host `evalWith`,
  generic in selector and value type, with `evalWith_rel`; registered in `ComputationalModels.lean` and
  `machine-library-design.md` §14.
- **P6-Q5, P6-Q6.** The formula-arithmetic layer over `TreeCircuit` in
  `Complexity/CircuitComplexity/FormulaArith/{Combinators,CarrySave,Compare,ModSum}.lean`, first rows of a
  circuit/formula gadget registry; O1 promotes the private `TreeNCAC.combine`; `Parity.lean`'s private XOR is
  re-pointed later (not here); `FormulaKit/Gate.lean` checked for reuse (r3 §H2: a different model).
- **P6-Q13.** `barrington` is computable, with the explicit conjugator `θ(σᵏ 0) = τᵏ 0`.
- **P6-Q14 B.** A generic **layering conversion** under `Complexity/` is part of 6a and Gate 45: double-NAND identity
  chains, with care for odd gaps (r3 §H3.13 resolves odd gaps by a parity twin and literal inputs).
- **P6-Q16 A.** NAND form is a predicate on `DAGCircuit` (`¬` gates of fan-in `≤ 2`); the conversion is an
  instance of `DAGCircuit.rewrite` with depth factor 2; NAND-form circuits are not `IsWellFormed` (disclosed).
- **P6-Q17 A.** Registry rows: H18 `BranchingProgram.evalWith`; H19 `runWith`/`runWith_rel`; H20
  `DAGCircuit.rewrite`. Records only.
- **P6-Q18 A.** Thm 2's circuit is a fan-in-2 `TreeCircuit` formula mirroring Bar89's three sections, reaching
  `Language.InNC 1` through `Language.InTreeNC.inNC`.
- **Location ruling.** Branching programs, Barrington, the NAND conversion (and, by P6-Q14, the layering) live in
  `Complexity/`.

Not in this job: P6-Q7 (O2, `decode_iff_mem_Ico`), P6-Q8–Q12 and Q15 (6b), and P6-Q19 (Gen09, which concerns only
6b docstrings). Nothing in this job depends on Gen09; cite no `[Gen09]`.

## Feasibility and size (maintainer's assessment)

Feasible. Everything is statements and definitions; the only proofs are the readers (mostly `rfl` or `Iff.rfl`),
the definitions' own obligations (termination, structure fields where you can prove them) and O1, which moves
proved code. Estimated surface: about **1,600–2,100 lines** in 11 new math files and 2 facades, plus O1 (about 180
lines moved). The heavy items are the definitions with bodies: the computable `barrington` and `conjugator`, the
midpoint-split `compTree`, `nandGadget` in `rewrite`'s gadget shape, the layering's column fold, and the formula
arithmetic. The root build (1,340 modules, one at a time) is long but mechanical.

## Branches, series and delivery

- **Checkout.** In your own clone, fetch `cryptography/pass-shelat-ch2-4` and start at the exact issue base. Read
  `policy.md`, the addendum and this brief. Record the base in `REPORT.md`.
- **Series 1, O1** (`owner/o1-balanced`, from the issue base): only O1 (*O1* below). Proved; no `sorry`.
- **Series 2, statements** (`stmt/gsw-6a`, from series 1's head): every 6a file and the registrations. Suggested
  commits, each compiling: (1) `BranchingPrograms/Defs`, `Eval`; (2) `Barrington`, `BarringtonConverse`, `NC1` and
  the facade; (3) `NANDForm`, `NANDLayering`; (4) the rest of `FormulaArith`; (5) the facades' imports,
  `ComputationalModels.lean`, `TCSlib.lean` and the `machine-library-design.md` rows.
- Keep both branches local. Commit them with `git -c commit.gpgsign=false`. The maintainer opens O1 and the
  statement PR (stacked on O1) after review; Seyoon approves and merges.
- **Deliver** every checkpoint and the final only under `inbox/fills/gsw-6a-statements/` on
  `exchange/pass-shelat-ch5-8`:
  - `REPORT.md` (*Report*);
  - `patches/o1/` (`git format-patch <base>..owner/o1-balanced`) and `patches/stmt/`
    (`git format-patch owner/o1-balanced..stmt/gsw-6a`), each with a `COMMITS.tsv`: one row per commit with its
    hash, the author's name, email and date, the committer's name, email and date, and its **signing** (`none`, or
    the format), so that `git am` reproduces every hash. Check the reproduction of both series in a scratch clone
    before you push, and say so in `REPORT.md`;
  - `src/`: every new or changed file at the `stmt/gsw-6a` head, under its repository path; `src-o1/`: the four
    files O1 changes, at the `owner/o1-balanced` head;
  - `evidence/`, with its manifest `evidence/SHA256SUMS` (*Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file except itself. The delivered paths must **equal** the
    manifests' paths: nothing missing, nothing extra, no leading `./`. Check this before each push.
- Commit on the exchange as `stmt gsw-6a: checkpoint N` and `stmt gsw-6a: final`. Pull with rebase before pushing;
  push only your path; never force-push; never touch another path (other fills, gates, `arora-barak-ch3-4/`,
  `lwe-sis-constructions/`). If a push is refused, keep the commit and say so.

## Base and parallel work

- **Open PRs at issue** (all based on the records branch or stacked on one): #331 (pairing statements:
  `Cryptography/Pairing/`, `KeyExchange/`, `AdvancedEncryption/IdentityBased/`, and an import hunk in `TCSlib.lean`'s
  Cryptography block), #338 and #339 (GSW fills: `GSW/*.lean`, `Hashing/SIS/Columns.lean`), #340 (stacked on #331:
  `Pairing/Assumptions.lean`) and #341 (sc-yao: `SecureComputation/Yao/**` and
  `Complexity/CircuitComplexity/Uniform.lean`).
- **6a is disjoint from them.** It edits only new files under `Complexity/`, `TreeNCAC.lean` (O1), the facade
  `CircuitComplexity.lean`, `ComputationalModels.lean`, `TCSlib.lean` and `machine-library-design.md`. The one shared
  path is `TCSlib.lean` with #331: put the new `import TCSlib.Complexity.BranchingPrograms` in the Complexity block
  (after line 27), well away from #331's hunk at line 75. 6a neither edits nor imports #341's `Uniform.lean`.
- If any of these PRs merges during the job, **stay on the issue base**; the maintainer rebases at landing.
- **Nothing of 6b.** No file under `Cryptography/`, no O2, no `[Gen09]`.

## Scope

**New files** (namespaces per r3 §H4; the model types `BranchingProgram` and `BranchingProgramFamily` at the root,
registered; their operations in `BranchingProgram`; circuit material in `BoolCircuit`; language classes in
`Language`, as `NCAC.lean` does):
- `TCSlib/Complexity/BranchingPrograms.lean` (facade, new topic) and `TCSlib/Complexity/BranchingPrograms/`
  `{Defs,Eval,Barrington,BarringtonConverse,NC1}.lean`;
- `TCSlib/Complexity/CircuitComplexity/NANDForm.lean` and `NANDLayering.lean` (r3 §H4 item 3 gives the reasons for
  a sibling file);
- `TCSlib/Complexity/CircuitComplexity/FormulaArith.lean` (facade, created by O1) and
  `FormulaArith/{Combinators,CarrySave,Compare,ModSum}.lean` (`Combinators` created by O1, extended here).

**Changed files:**
- `TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean`: O1 only.
- `TCSlib/Complexity/CircuitComplexity.lean`: imports `FormulaArith` (O1), `NANDForm`, `NANDLayering`; its contents
  list.
- `TCSlib/ComputationalModels.lean`: **Models** `BranchingProgram w n` and `BranchingProgramFamily w`, importing
  `TCSlib.Complexity.BranchingPrograms.Defs`; **Conversions** `BranchingProgram.barrington`,
  `BranchingProgram.toFormula`, `BoolCircuit.DAGCircuit.toNANDForm`, `BoolCircuit.DAGCircuit.layerNAND` (alphabetical,
  in the file's style).
- `TCSlib.lean`: `import TCSlib.Complexity.BranchingPrograms` (policy §1, Exports).
- `machine-library-design.md` §14: rows **H18** (`BranchingProgram.evalWith` with `evalWith_rel`: contract, file and
  line, status "statement only, Gate 45", consumers: the Boolean semantics C8 and GSW's G2), **H19**
  (`runWith`/`runWith_rel`, `DAGCircuit.lean:149/625`, public, recorded by P6-Q17; consumers: `DAGCircuit.values`,
  `depths`, phase-5 `GSW.eval`, 6b's `fheEval`) and **H20** (`DAGCircuit.rewrite`, `DAGTransform.lean:246`, with
  `rewrite_eval`/`_depth_le`/`_new_gates`/`_length_le`; consumers: `binarize`, `deMorgan`, `toNANDForm`); a sentence
  in the registry's status paragraph; and a new subsection "Circuit and formula gadgets" whose first rows are the
  `FormulaArith` gadgets (`balanced`, `neg`, `subst`, `rename`, `and2`/`or2`/`xor2`/`xor3`/`maj3`, `csaStep`,
  `csaReduce`, `carryOut`, `geConst`, `modSumInterval`), each with file, contract and depth (P6-Q6). Records only;
  keep the document's style.

**Frozen:** everything else, including `DAGCircuit.lean`, `DAGTransform.lean`, `DAGFanin.lean`, `TreeDAG.lean`,
`Basic.lean`, `NCAC.lean`, `Adder.lean`, `Parity.lean`, every file under `Cryptography/` and `blueprint/`.
- **Scope requests.** If a definition or statement needs a change to a frozen file, stop that line of work and ask
  Seyoon in your session with the file, the diff and the reason; proceed only on his approval, and record the
  request and answer verbatim under `evidence/scope-request/` and in `REPORT.md`. Seyoon prefers routes with no
  frozen-file edit.
- **Known reader gap, not to be fixed here.** `GadgetCorrect` (`DAGTransform.lean:68`) has no `_iff` reader; N2's
  fill will need one (r3 §H2). Your statements do not unfold it (N2 is admitted), so leave `DAGTransform.lean` alone
  and list the gap in the reader census.

## What to write

**For every file:** the policy header (copyright block, precise imports, the three `set_option` lines, a module
docstring with `# Title`, `## Main definitions`, `## Main results`, `## References` with full citations of every tag
used: [Bar89], [BV14], [BV11], [AP14] as cited, [AB09] only where an existing tag is kept). Lines of at most 100
characters (Python `len`); every file under 1000 lines, target 150–600 filled (r3 §H7 gives the expected sizes).

**Definitions.** Every r3 definition gets its body now, total and, where r3 says so, computable (`barrington`,
`conjugator`, `nandGadget`, `layerGates`, the formula arithmetic; `toFormula` may be `noncomputable`). Each new
public `def` lands with its readers, **proved**: `_eq` by `rfl` where that holds, case lemmas covering every input,
`_iff` for predicates (`Iff.rfl`), non-simp `simps` for structures. No `@[simp]` and no global attribute. Each
reader's docstring states its formula. Where a definition must carry a proof (a structure field such as
`DAGCircuit.args_lt`, an `Equiv`'s inverse laws), prove it now if you can; otherwise state it as a **target** lemma
that the definition cites, as r3 does for `toNANDForm` (N2) and `layerNAND` (N12–N13), and list every such
definition in the axiom report. Termination proofs are never admitted: they must be real.

**Targets.** Every r3 target (C1–C25, N1–N13, F1–F3, F5–F10, each row possibly several lemmas) is a `theorem` whose
body is `sorry`, with a docstring that:
1. opens with the statement in words, its formula written out (arguments in Lean order);
2. gives the `[TAG, location, anchor]` tag from r3 (anchors per r3 §H1), or says "Glue" for technical lemmas (the
   NAND and layering conversions, the host readers, as r3 marks them);
3. states every deviation from the source (r3 lists them: BV14's instruction order against Bar89's, program order,
   `σ 0` reading, the OR case through Lemma 2, the formula form of Thm 2, NAND form not well-formed, literal inputs
   for the layering);
4. ends with a `**Proof sketch.**` paragraph naming the steps a fill will follow (policy §3), with the readers and
   host lemmas it will use. The sketch is the fill's plan; a target whose sketch you cannot write is not ready.

**Names and shapes** are fixed now. Adjust a name, binder or argument order where Lean requires it, keeping the
meaning; record each change in `REPORT.md` § *Statement changes against r3* with the reason (the GSW statement
phase's QS1/QS2 are the precedent). A change of meaning (a weaker or stronger statement, a new hypothesis) needs a
probe that shows r3's form false or unprovable, and goes to Seyoon as a question in the report; never silently.
Settle every constant marked *(fix)* by hand and with `decide` checks, and record the derivation.

**File-specific notes** (r3 has the statements; these are the known pitfalls):
- **Defs.** `BranchingProgram` wraps `instrs : List (Instr w n)`; give it an `Append` instance with its reader so
  `B₁ ++ B₂` is notation. `yield` composes in program order: `yield_append` is `B₂.yield x ∘ B₁.yield x`.
  `conj θ` conjugates both maps of every instruction; `complementLast σ` post-composes the last instruction's maps
  with `σ⁻¹` (Bar89's `μσ⁻¹` read left to right). Families recognize by accepting sets (`x ∈ L ↔ B(x) ∈ F_n`).
  `InBWBP`/`InPBP` use explicit polynomial length bounds (`length ≤ a·(n+1)^k`).
- **Eval.** `stepWith` is the push form of r3 §H3.5 with `Finset` sums; `evalWith` folds it in program order.
- **Barrington.** `IsFiveCycle σ := σ.cycleType = {5}` (decidable). `sigma1 = c[0,1,2,3,4]`,
  `sigma2 = c[0,2,4,3,1]` (Bar89's `(12345)`, `(13542)`, 0-based). The commutator in program order is
  `sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1` (Mathlib's product applies the right factor first) and equals
  `c[0,2,1,4,3]`, Bar89's `(13254)`. `conjugator σ τ` must be an `Equiv.Perm (Fin 5)` built computably from
  `θ(σᵏ 0) = τᵏ 0` (not `Equiv.ofBijective`, whose inverse is noncomputable); define it for every pair (for example
  with the identity when either is not a five-cycle) and state C10 under `IsFiveCycle` hypotheses. `barrington` is
  total on every `TreeCircuit` (fan-in above 2 is unconstrained by the theorems, which assume `c.maxFanin ≤ 2`);
  literals `⟨i, 1, σ⟩`/`⟨i, σ, 1⟩`; constants `⟨0, σ, σ⟩`/`⟨0, 1, 1⟩` under `[NeZero n]`; the OR case by De Morgan
  through `complementLast`, with the outputs chosen so that the result has output `σ` (r3 §H5.3).
- **BarringtonConverse.** `compTree` splits the instruction list at the midpoint (termination on length); the empty
  list gives the identity wires. `wireComp` uses O1's `TreeCircuit.balanced`.
- **NC1.** The class statements route through `Language.InNC.inTreeNC_one` (NC¹ ⊆ PBP₅) and
  `Language.InTreeNC.inNC` (BWBP ⊆ NC¹); the `n = 0` case through the accepting set.
- **NANDForm.** `nandGadget n : DAGGate → List DAGGate → List DAGGate × ℕ` per r3 §H3.9's table, in the style of
  `deMorganGadget` (`DAGFanin.lean:475`); `toNANDForm` is `C.rewrite (nandGadget n) nandGadget_correct hC`.
- **NANDLayering.** r3 §H3.13 and §H5.6b exactly: `IsLayered`, `litInput`, the column fold `layerGates` and
  `layerOutput` (computable, every gate emitted as `⟨.not, args⟩`, no NAND-form hypothesis in the definitions), and
  `layerNAND` with the fields N12–N13. Name it `layerNAND`, never `toLayered` (taken by `LayeredDAG.lean:208`).
  The parity twin and the literal inputs are not optional: over positive inputs only, no layering exists in general
  (r3 §H3.13, the odd-gap finding); probe P9 checks this design.
- **FormulaArith.** `Combinators` adds `neg`, `subst`, `rename`, `const`, `and2`, `or2`, `xor2`, `xor3`, `maj3` to
  O1's `balanced`; `CarrySave`, `Compare` and `ModSum` per r3 §H5.7, with semantics through `Adder.lean`'s `bitsVal`
  and `carryBit` (read through their published readers; list any missing in the census). No depth term linear in
  `log q` (r3 §H3.3); the closed forms F6, F10 are *(fix)*.

## O1 (series 1; owner-side, proved)

Move `TreeNCAC.lean:172–351` (the section "Simulating an unbounded gate by a balanced binary tree": `pairUp`,
`combineFuel`, `combine` and their lemmas) into the new
`FormulaArith/Combinators.lean`, and create the facade `FormulaArith.lean` (`## Contents`: `Combinators`), imported
by `CircuitComplexity.lean`.
- `combine` becomes the public `BoolCircuit.TreeCircuit.balanced`, and its four lemmas the public `balanced_eval`,
  `maxFanin_balanced_le`, `depth_balanced_le`, `size_balanced_le` (r3 §H5.8), each with a formula docstring. Add the
  readers `balanced_nil : balanced b [] = .node b []` and `balanced_singleton : balanced b [c] = c` (by `rfl`).
  `pairUp`, `combineFuel` and their lemmas stay `private` helpers.
- **The proofs move byte-identical** except three Rule 10 repairs: the reads `simp [pairUp, TreeCircuit.eval]` and
  `simp only [pairUp, TreeCircuit.eval, …]` (`TreeNCAC.lean:195`, `:199`) and `simp [combineFuel, TreeCircuit.eval]`
  (`:261`) go through the published readers `TreeCircuit.eval_node_true`/`eval_node_false` (`TreeDAG.lean:126/132`)
  or `eval_node_true_iff`/`_false_iff` (`Basic.lean:155/163`). `Combinators.lean` may import `TreeDAG` (no cycle:
  `TreeDAG` imports only `DAGCircuit` and `Basic`).
- `TreeNCAC.lean` imports `Combinators`; `toBinary` uses `TreeCircuit.balanced` and the public lemmas; every other
  declaration of the file, and every `toBinary_*` statement, stays byte-identical. The line 366 read in the
  untouched `eval_node_map` stays as it is (recorded for clean-up part 2).
- Evidence: a byte comparison of the moved block (old against new, after the renames) showing exactly the three
  repairs; the header check of `TreeNCAC.lean`; seals of `Combinators.lean` and `TreeNCAC.lean`; axioms standard
  only; no duplicate left behind.

## Multi-agent work (ruling: up to 2 sub-agents)

- **The lead owns the job:** the brief, both branches, every commit, the integration, the root build, the seals, the
  delivery and `REPORT.md`. Only the lead commits on `owner/o1-balanced` and `stmt/gsw-6a` and pushes.
- **Suggested split** (disjoint files; another disjoint split is fine if recorded): the lead does O1 first, then
  `NANDForm`, `NANDLayering`, the registrations and the §14 rows; sub-agent A writes `BranchingPrograms/` (five files
  and the facade) from O1's head; sub-agent B writes `FormulaArith/{CarrySave,Compare,ModSum}` and the F1–F3 part of
  `Combinators`.
- **Worktrees and olean trees.** Each sub-agent has its own git worktree of the lead's clone (on a sub-branch from the
  lead's current commit) and its own TCSlib olean tree (`TCSLIB_OLEANS`); `.lake/packages` is a symlink to the lead's;
  only the lead runs `lake` and fetches the cache. The lead may seed a sub-agent's tree by copying its own
  bootstrapped **TCSlib** olean tree; never copy Mathlib or package trees.
- **One Lean process at a time on the host**, for all agents together, through one lock (for example
  `flock <clone>/.lean.lock …`), released between modules.
- Sub-agent logs go under `evidence/subagents/<name>/`; `REPORT.md` records who wrote what.

## Checks and evidence

Run Python as `python3 -I`. Never run `lake build` or an unfiltered `lake exe cache get`; check one module at a time
with `scripts/lean_check_tree.sh` (the addendum). Count errors in both forms (`^\S+\.lean:\d+:\d+: error[:(]`) in
every log, and keep every raw log.

1. **Build of the closure.** Bootstrap the prefix of `order.txt` the new files need, insert the new modules after
   their imports (facades after their children), check every new and changed module, then every module downstream
   of a changed one (`TreeNCAC`'s downstream, the facades `CircuitComplexity` and `ComputationalModels`).
   `evidence/build/summary.txt` gives each module's return code, error count and `sorry` warnings, for the O1 head
   and for the final head.
2. **Build of the root.** Build the rest of `order.txt` and `TCSlib` last, from the final head:
   `evidence/build/root/summary.txt`. If the host cannot finish, see the addendum's adaptation.
3. **Statement list.** `python3 -I briefs/pass-shelat-ch5-8/maintainer/tools/decls2.py . <base> <files…>` over every
   new and changed Lean file (ADDED/CHANGED/REMOVED against the base), and a `StmtDump` probe printing every new
   constant with its full name and type (the GSW statement phase's `probe/StmtDump.lean` in
   `briefs/lattice-gsw/statement-phase/evidence/stmt-gsw.zip` is the model). `REPORT.md` maps each r3 target row
   (C1–C25, N1–N13, F1–F3, F5–F10) to its declarations, and lists the definitions with their readers.
4. **Admissions.** The base's `sorry` declarations are in `base-sorries.txt` (a syntactic scan of the 1,340 modules:
   229 in 52 modules, none under `CircuitComplexity/`). At the final the warnings of the root build must be exactly
   those plus the new targets; at the O1 head, exactly those. List the new ones per module.
5. **Axioms.** Print the axioms of every declaration and auxiliary constant of the new and changed modules (the
   `AxiomProbe.lean` of the same zip is the model). Expect `propext`, `Classical.choice`, `Quot.sound` only, except
   `sorryAx` in exactly the targets and in the definitions that cite a target proof (r3: `toNANDForm` through N2,
   `layerNAND` through N12–N13; any others you add) and their dependents. Run a **dependency trace** that walks
   each constant's closure and names, for every constant reaching `sorryAx`, the targets through which it does. O1's
   constants: standard axioms only.
6. **Rule 10.** Readers only for other files' definitions (policy §1; core and Mathlib definitions may reduce in a
   `rfl`, `decide` or `show` step but are never passed to `simp`, `rw` or `unfold`). Each new file may read its own
   definitions directly; the new files are foreign to each other.
   - Whole-file seals A and B of every new and changed Lean file over its full TCSlib import closure, strict and coe
     variants (the coe-variant seal A canonical), with `-DmaxErrors=0`, collected from the elaborated terms plus
     compiler-generated matchers, and the explicit-unfold scan. The tools of the GSW statement phase (`tools/xr/` in
     `stmt-gsw.zip`: `mkcollect.py`, `mkseals_ab.py`, `mkseals_coe.py`, `runner_full.py`, `sealsum.py`) are the
     model; adapt their paths.
   - **Paired controls on every new owner** (the 11 new math files, `Combinators.lean` included): a negative control
     that reads one of its definitions from another file by `rfl`/`Iff.rfl`/`unfold` (passes unsealed, fails sealed
     exactly once) and a positive control that uses its published reader (passes sealed). A file that defines
     nothing gets no pair, and the report says so.
   - **Notation, never sealed:** reducible abbreviations, `PolyExpr.eval`, projection coercions.
   - **Reader census:** for every foreign definition that a target's sketch or a definition's body reads, its
     reader (`path:line`) or MISSING with the proposed reader. Expected MISSING: `GadgetCorrect` (r3 §H2).
7. **Probes** (under `evidence/probes/`, outside the library, checked against the final tree; kernel `decide` or
   `rfl` only, never `native_decide`; where the kernel cannot reduce a definition, `#eval` output recorded as
   evidence, never as a proof). One probe for each statement that could be wrong:
   - P1 *yield order*: Bar89's example (`p004-b001`, BV14 order) yields `c[0,2,1,4,3]` exactly on `x₁ = x₂ = 1` and
     the identity elsewhere; Bar89's width-2 XOR example (`p001-b002`, translated to BV14's order and 0-based
     variables) yields the transposition exactly when `x₇ ⊕ ¬x₄ ⊕ x₈`; `yield_append`'s direction on a two-program
     example.
   - P2 *commutator*: `sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1 = c[0,2,1,4,3]` (Bar89's `(13254)`); the right-to-left
     reading gives `c[0,3,2,4,1]` (`(14352)`); `IsFiveCycle` of `sigma1`, `sigma2` and the commutator.
   - P3 *conjugator*: computable; `conjugator σ τ * σ * (conjugator σ τ)⁻¹ = τ` for all 24 × 24 pairs of
     five-cycles (record the time; if `decide` is too slow, `#eval` the check and keep C10's statement).
   - P4 *Lemma 2*: `complementLast` on a sample program: yield `σ⁻¹ ∘ B(x)`, so identity on `A` and `σ⁻¹` off it.
   - P5 *Theorem 1*: `barrington` on `x₀ ∧ x₁`, `x₀ ∨ ¬x₁`, both constants, a fan-in-1 node and a depth-2 formula:
     five-cycle recognition with output `σ`, `barrington_yield_zero`'s reading, and length against `4^depth`, on
     every input.
   - P6 *host*: `evalWith_single` (C8) on a non-permutation program (a constant map), and C6's pull form on a
     permutation instruction.
   - P7 *Theorem 2*: `compTree` (and `toFormula` if computable) on P1's XOR program: the wires and the acceptance
     formula agree with `yield` on all inputs; the depth bounds C19, C21 on these instances.
   - P8 *NAND gadget*: every row of r3 §H3.9's table (`∧`, `∨`, `¬` with 0, 1, 2 and repeated arguments): the
     emitted gates evaluate to the old gate on all inputs, add at most 2 levels and at most `fan-in + 2` gates.
   - P9 *layering*: `layerNAND` on an XOR circuit in NAND form, on a circuit with an odd gap and on one with a
     fan-in-0 gate: `eval (litInput x) = C.eval x` on every input, `IsLayered` and `IsNANDForm` (decide), depth
     equal to `C.depth`, size within N11.
   - P10 *formula arithmetic*: `xor3`/`maj3` truth tables; `csaStep`'s value equation, `carryOut` against
     `carryBit`, `geConst`, and `modSumInterval_eval` exhaustively for small `q` (2 to 7), `N ≤ 3`, all `a`,
     `lo ≤ hi ≤ q`; the closed forms of F6 and F10 numerically on a range.
8. **Frozen-file check.** A `python3 -I` script that extracts every declaration of each changed existing Lean file
   at base and final and compares headers (and whole definitions) byte for byte, allowing only O1's documented
   changes to `TreeNCAC.lean`; with two controls (one altered character reports exactly one difference; one deleted
   reader reports exactly one removal). Output under `evidence/headers/`.
9. **Lint.** `python3 -I scripts/style_lint.py <new and changed Lean files>`: 0 findings.
   `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity --check8b` at base and final; the maintainer's
   baseline at the issue base is **25 FAIL / 390 WARN over 500 files** (`TCSlib/Complexity/CircuitComplexity` alone:
   0 FAIL / 79 WARN over 104 files). Diff the line sets: no new FAIL line, and no new WARN line except one you
   disclose and justify.
10. **File sizes.** Lines and maximum width of every new and changed file, at both heads, with a `python3 -I`
    script; the expected filled size of each new file (r3 §H7).
11. **Name-clash scan.** No new name, public or private (namespaces resolved), is already declared in `TCSlib/` at
    the base; in particular none uses `NAnd` or `toLayered`. Script and output under `evidence/clash/`.
12. **Reuse and overlap** (`REPORT.md` § *Overlap and reuse*). Search first (the policy's duplication rule;
    undisclosed copies of public lemmas are majors). For every new declaration that restates, specializes or
    re-proves existing material, give its nearest relative (`path:line`), the relation and why it is not reused.
    Confirm or correct each r3 §H2 finding: the `NAndCircuit`/`toNAnd` clash; `toLayered`/`LayeredCircuit`;
    `combine` (O1) and `toBinary`; `Parity.lean`'s private `xorNode`/`IsDual` (not copied); `BinArith.carry`/`sumBit`;
    `FormulaKit/Gate.lean`; `dnfDAG`; `stdGateOps`; `SLOp`; `unfoldGate`; `StraightLine.dualRail`; `Adder.lean`'s
    `bitsVal`/`carryBit`. List the searches you ran.

**Checkpoints** (at least one mid-way): checkpoint 1 is O1 complete (its series, checks 1, 5, 6, 8 for it) with
`BranchingPrograms/Defs`, `Eval` and `NANDForm` compiled; the final has everything.

If a probe shows an r3 statement false, stop that line, keep r3's form out of the branch, and put the counterexample
and your proposed statement in `REPORT.md` as a question for Seyoon. Do not weaken a statement silently.

## Sources and citations

- Cite only ingested passages: [Bar89] (`inputs/`), [BV14], [BV11], [AP14] at the base, with the anchors of r3
  §H1. **Never fabricate** a quotation, location or anchor. Glue declarations carry no tag and say "Glue".
- Do not add reference files, edit `blueprint/` or run `scripts/sources.py`.
- Bar89's instruction lists the `x_j = 1` map first; BV14's lists the `0` map first; the model follows BV14 and the
  docstrings disclose it. Bar89's products read left to right (r3 §H3.6 and the ingest's transcription note).
- Identifiers use Greek `μ` (U+03BC), never the micro sign.

## Report

`REPORT.md` gives: the base and both heads; who wrote what; the statement list (check 3) with the r3 row map; the
definitions and their readers; § *Statement changes against r3*; the constants settled; the builds of the closure
and the root (checks 1–2); `sorry` and admission counts (check 4); the axioms and the dependency trace (check 5);
the Rule 10 seals, controls and reader census (check 6); the probes (check 7); the frozen-file check; lint; file
sizes; § *Overlap and reuse*; § *Scope requests* (none, or each with Seyoon's answer); questions for Seyoon, if any;
the evidence, with its manifest.

### Evidence completeness

Every file that `evidence/SHA256SUMS` names is delivered: seal and control sources, manifests and request records,
the header check with its output and controls, the clash scan, the dependency trace, every raw log and results
file, sub-agent logs, the probe sources and the tools used. If the evidence is too large for one commit, deliver it
in several commits or numbered ZIP parts, each with an entry list; leave nothing out for size. Check before each push
that the delivered paths are exactly the manifests' (top level and `evidence/`), with no leading `./`.

The maintainer replays both series on the then records tip, rechecks the library root, and opens O1 and the statement
PR for Seyoon.

**Ready to dispatch**
