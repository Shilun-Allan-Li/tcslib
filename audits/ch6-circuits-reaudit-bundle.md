# External re-audit pack — Chapter-6 circuit surface, round 2

Audits commit `12ff3add` on `complexity/arora-barak-ch1`. Round 1
(pack `audits/ch6-circuits-pack.md`, auditing `28690c01`) returned
**0 blockers, 4 majors, 7 minors, 4 notes**
(`audits/ch6-circuits-findings.md`, attached verbatim); the gate stayed
open. All fifteen findings were accepted after source verification; none
was contested. The repairs — commit `12ff3add`, **documentation only,
zero Lean statements changed**, as §5 of the findings permits for
deliberately deferred bridges — are itemized in
`audits/ch6-circuits-resolutions.md` (attached), which also acknowledges
the two round-1 **pack errata** (the §6.5/§6.6 misplacement and loose
item ranges of finding 10; the 22-vs-23 sweep-list count of finding 11,
explained there). The sent round-1 pack is immutable per protocol.

## Repository-side attestations (maintainer, local machine — verify or challenge)

1. **Freeze.** `12ff3add` touches, relative to the audited `28690c01`:
   eleven in-scope Lean files, the facade, the catalog, and
   `backlog.md` §3 — docstrings, module-docstring ledgers, and one
   section header only. `git diff 28690c01..12ff3add` contains no change
   to any `def`/`theorem`/`lemma`/`structure`/`instance` signature or
   body. Zero sorries in scope, as before.
2. **Elaboration.** Post-repair fresh-olean sweep, Lean 4.25.0 / mathlib
   `029db123ddaa`: the 22-entry circuit list, the 31 Switching/LMN
   reverse-dependency modules, and the catalog — 55 modules, zero
   `error:` lines.
3. **Policy.** Style lint: 0 FAIL / 0 WARN over the `CircuitComplexity/`
   directory, unchanged.

## What round 2 asks

This is a **verification round**, not a fresh audit. The round-1 attack
results (§3 of the findings: all guards held) and the verdicts already
*faithful* or *faithful-with-declared-divergence* are settled unless a
repair touched their text. Tasks:

1. **Majors 1–4.** For each, judge whether the repair discharges the
   finding: the wrapper re-description and its catalog/module-docstring
   propagation (finding 1); the normal-form re-attribution and the
   three-carrier metric ledger (finding 2); the restriction of
   preservation claims to the polynomial union and the de-identification
   of `InSIZE` from AB's fixed `SIZE(T)` in `PPoly.lean`, `Hierarchy.lean`,
   and the facade (finding 3); the hard-function incomparability rewrite
   and the facade's "tree-circuit analogue" phrasing (finding 4).
2. **Re-issue the task-1 verdicts** for [AB09] Def 6.1 and Def 6.2 — the
   two *divergent-undeclared* rows — and the Thm 6.21 row, against the
   repaired ledgers.
3. **Sweep the minor repairs** (findings 5–10 as itemized in the
   resolutions file) for correctness and completeness, including that no
   repair introduced a new misstatement.
4. **Confirm the recordings**: notes 12–15 in `backlog.md` §3 (excerpted
   in the resolutions file), and the two pack errata as acknowledged.
5. **Residual pass.** Anything newly visible in the repaired prose that
   round 1's severity scheme would catch.

Severity scheme and response format as in round 1; findings to
`audits/ch6-circuits-reaudit-findings.md`. The gate closes on zero
blockers/majors in this round.

## ===== audits/ch6-circuits-findings.md =====

# Chapter 6 circuit surface: external semantic audit

**Disposition: gate remains open.** Findings: **0 blockers, 4 majors, 7 minors, 4 advisory notes**. The majors concern the advertised circuit conversion, the normal-form substrate's interpretation, fixed size classes, and the interpretation of the hard-function result. None alleges a faulty Lean proof or an escape through the class predicates' basis/finiteness guards.

Audited input: `ch6-circuits-bundle.md`, representing commit `28690c01` on `complexity/arora-barak-ch1`.

Bundle SHA-256: `51d2d1bb9a90dbac59a7a123887562004ab90a42f171da0b5aff9a2478d5e055`.

All 16 advertised attachments are present: 13 content modules, their facade, the catalog, and the sweep list. All definitions and theorem signatures in the 14 in-scope Lean files were examined. Proof correctness and the closed Chapter-1/2 gates were accepted as commissioned. A comment/string-aware source scan found no `sorry`, `admit`, `sorryAx`, new `axiom`, or `native_decide` tokens in these 14 files. This is a source observation, not a fresh elaboration or transitive axiom check. The bundle supplies attestations, not a checkout, `.olean` files, or the raw sweep/axiom logs; their provenance was not independently reproduced. Finding 11 records a checkable discrepancy in one attestation.

References of the form `Basic.lean:48-55` mean `TCSlib/Complexity/CircuitComplexity/Basic.lean:48-55`. Source line 1 is the first source line after its attachment header, excluding the separating blank line. Pack references use the original bundle's line numbers. No uploaded source was changed. Catalog observations are included only where requested by Brief task 4; the catalog's implementations and other imported developments were not audited.

## 1. Book baseline and per-item verdicts

The baseline was checked against the **published 2009 numbering**, rather than the differently numbered Princeton draft. These are independent mathematical restatements; the next column describes the actual Lean surface. Polynomial classes use the usual asymptotic interpretation, with finite-length conventions handled separately. The hierarchy row records the book's displayed size-range condition.

| Book item | Book restatement | Lean comparison | Verdict |
|---|---|---|---|
| Definition 6.1, p.107 | Finite DAG; $n$ sources, one sink; AND/OR fan-in 2, NOT fan-in 1; size counts vertices. | `FeedForward` is a generic operation model; finite `stdGateOps` families provide the relevant Boolean specialization. Layering, unbounded fan-in and non-input counting are declared. Additional structural conventions need disclosure: finding 5. | **divergent-undeclared** — residual conventions, not an unrestricted-gate class |
| Definition 6.2, p.108 | $L\in\mathrm{SIZE}(T)\iff\exists(C_n)\ \forall n\ \forall x\in\{0,1\}^n:\ \lvert C_n\rvert \le T(n)\ \land\ (C_n(x)=1\iff x\in L).$ | Quantifiers and exact recognition agree. The size budget is measured in a different model; it is not the same fixed class. `PPoly.lean:38` and `Hierarchy.lean:42-44` obscure this. Finding 3. | **divergent-undeclared** — effects on fixed `SIZE(T)` are misrepresented |
| Definition 6.5, p.108 | $\mathrm{P/poly}=\bigcup_c\mathrm{SIZE}(n^c)$. | `InPPoly` uses finite standard-gate families and a single bound $a(n+1)^k$. These are appropriate polynomial-class conventions; no advice characterization is asserted. `PPoly.lean:69-73,95-121`. | **faithful-with-declared-divergence** |
| Definition 6.9, pp.110-111 | $\mathrm{CKT\text{-}SAT}=\{\langle C\rangle:\exists x,\ C(x)=1\}$. | `CktSat` is typed tree satisfiability; `cktSatLang` is its canonical encoded image. Tree rather than DAG, encoding choice, and the absence of a polynomial-time reduction are declared. `CircuitSat.lean:28-53,73-79`; `Encoding.lean:230-301`. | **faithful-with-declared-divergence** |
| Definition 6.24, p.117 | Polynomial-size, bounded-fan-in, depth $O(\log^d n)$ families define $\mathrm{NC}^d$; $\mathrm{NC}=\bigcup_{i\ge1}\mathrm{NC}^i$. | Same resource/quantifier pattern, but restricted to trees, with repaired logarithms. The ledger expressly declines identification with the book's DAG classes. `NCAC.lean:34-72,113-149`. | **faithful-with-declared-divergence** — tree variant only |
| Definition 6.25, p.118 | Allow unbounded AND/OR fan-in for $\mathrm{AC}^i$; $\mathrm{AC}=\bigcup_{i\ge0}\mathrm{AC}^i$. | `InAC` removes only the fan-in predicate from the tree-family definition; the union includes level zero. Same declared model restriction. `NCAC.lean:135-159`. | **faithful-with-declared-divergence** — tree variant only |
| Claim 6.8, p.110 | $L\subseteq\{1^n:n\in\mathbb N\}\Rightarrow L\in\mathrm{P/poly}$. | `inPPoly_of_le_allOnes` says exactly this, using the declared `P/poly` conventions. Both inclusion in the unary language and rejection of other words are enforced. `UnaryLanguages.lean:191-224`. | **faithful** |
| Theorem 6.21, p.115 | $n>1\Rightarrow\exists f:\{0,1\}^n\to\{0,1\},\ \forall C,\ \lvert C\rvert \le2^n/(10n)\Rightarrow\exists x,\ C(x)\ne f(x).$ | `exists_hard_function` quantifies over trees, uses natural-number division by $n+5$, and includes vacuous small arities. The model change is declared, but the ledger's comparison and facade need correction: finding 4. | **faithful-with-declared-divergence** — counting analogue, not the DAG theorem |
| Theorem 6.22, p.116 | $2^n/n>T'(n)>10T(n)>n\Rightarrow\mathrm{SIZE}(T)\subsetneq\mathrm{SIZE}(T')$. | `treeSize_ssubset` instead requires a padding function, an upper bound at every length, and a counting inequality at one length; its classes are tree size classes. The file explicitly says this is not the book theorem. `Hierarchy.lean:40-78,289-306`. | **not-the-claimed-item** — explicitly and correctly unclaimed |

“Faithful-with-declared-divergence” approves the disclosed variant as a variant; it does **not** certify equivalence to the book's model. In particular, neither the higher tree `NC`/`AC` levels nor the tree hard-function theorem can silently substitute for their DAG counterparts.

The anchors for Example 6.3, Claim 6.8, Definition 6.9, Lemma 6.11, Definitions 6.24-6.25, and Example 6.26 refer to the right items. Lemma 6.11 is a polynomial-time reduction; the repeated restriction here to equisatisfiability and clause counts is appropriate. The incorrect section/type mappings are recorded in finding 10.

## 2. Numbered findings, in severity order

### 1. MAJOR — `toFeedForward` is a whole-function gate wrapper, not the advertised structural embedding

**Locations:** `FeedForward.lean:17-20,129-132,280-307,329-338`; corroborating disclosure at `Hierarchy.lean:45-49`. The same misleading description appears in `TCSlib/ComputationalModels.lean:72-73`.

The definition installs

```lean
op := { ι := Fin n, func := C.eval }
```

at the first non-input layer and puts one identity gate at every subsequent layer. Consequently,

$$
\operatorname{size}(C.\mathrm{toFeedForward})
=\operatorname{depth}(C.\mathrm{toFeedForward})
=C.\mathrm{depth}+1.
$$

It neither embeds the source gates nor pads shorter source branches. For example, the tree $x_0\lor x_1$ becomes a single OR operation followed by an identity. After Boolean alphabet transport, this two-input operation is not a member of `stdGateOps`: its arity excludes identity/NOT and its value at $(0,1)$ differs from the two-input AND. More generally, `universalCircuit f` has depth at most two, so this wrapper gives **every** Boolean function a generic feedforward circuit with at most three gates. That is possible because its first gate is unrestricted.

There is also a direct numerical counterexample to the prose bound `C.size * C.depth`: for a literal,

$$
C.\mathrm{size}=1,\quad C.\mathrm{depth}=0,\quad
\operatorname{size}(C.\mathrm{toFeedForward})=1>1\cdot0.
$$

The formal theorem uses `C.size * (C.depth + 1)` and is not contradicted. Likewise, its formal depth theorem correctly includes the extra layer. The defect is the conversion's advertised meaning and its usefulness as a circuit-model bridge, not those proved statements.

**Impact:** This map cannot discharge `OnlyUsesGates stdGateOps` in a future complexity-class inclusion. It does **not** currently smuggle arbitrary gates into `InPPoly`, whose guard remains explicit. `Hierarchy.lean` already recognizes the problem; that disclosure must reach the defining module and catalog.

**Repair:** Either rename/document this as a semantic wrapper into unrestricted gates, removing the faithful-embedding and incorrect depth/size claims, or implement an actual node-by-node embedding and state basis preservation, finiteness, evaluation, and resource bounds. Gate closure does not require implementing the future bridge if the existing wrapper is accurately quarantined.

### 2. MAJOR — the normal forms do not implement the attributed layered model, and their size/depth conventions are incompletely disclosed

**Locations:** `Basic.lean:46-55,325-341,374-401,641-651`; pack `ch6-circuits-bundle.md:89`.

The ledger identifies `NAndCircuit`/`NOrCircuit` with [OD14] Definition 4.26's alternating **layered** circuits. Their constructors enforce alternating parent/child connectives, but do not impose a common input layer or equal root-to-literal path lengths. For instance, an AND root may have both an OR clause child and an OR node whose child is an AND clause. Its two literal paths have different lengths. Additional padding is required to obtain the attributed layered object.

The measures also require separate descriptions. For an `NAndCircuit.clause` containing two distinct positive literals,

$$
c.\mathrm{size}=1,\quad c.\mathrm{depth}=0,
\qquad
c.\mathrm{toCircuit.size}=3,\quad c.\mathrm{toCircuit.depth}=1.
$$

`Circuit.size` counts literal occurrences; normal-form `size` does not. Normal-form depth gives an entire nonempty conjunction/disjunction depth zero. Moreover, the normal-form size counts the output, whereas OD14's measure excludes both the input and output layers. The ledger's unqualified description of `size` as counting leaves does not supply this accounting. Empty `.node []` and empty `.clause []` additionally have the same value and size but different normal-form depths, so a blanket depth-shift identity would also need qualifications.

**Impact:** A reader could substitute the normal-form parameters into a depth- or size-sensitive statement from OD14 with the wrong parameters. No downstream Switching/LMN proof is being audited here; the in-scope attribution and metric meanings are independently defective.

**Repair:** Describe these as alternating trees with base clauses, not a direct realization of Definition 4.26. Give separate ledgers for `Circuit` and the two normal forms: counted nodes, excluded literal data, included root, depth-zero base clauses, and missing global layering. Alternatively add a genuinely layered carrier and explicit parameter conversions. Keep the existing normalization theorems labeled with their actual source and target measures.

### 3. MAJOR — convention changes preserve the polynomial union, not fixed `SIZE(T)`

**Locations:** `PPoly.lean:20-21,36-46,107-116`; `SizeClasses.lean:116-117,151-157`; `Hierarchy.lean:42-44`; facade `TCSlib/Complexity/CircuitComplexity.lean:61-66`.

The assertion that all divergences are class-preserving is too broad in a file that defines and attributes `Language.InSIZE` to the book's exact size class. The bundle itself supplies a counterexample:

$$
\mathrm{Language.allOnes.InSIZE}(n\mapsto1).
$$

The baseline model counts its $n$ input vertices, so a size-one circuit is already impossible for $n\ge2$. Thus this fixed class differs before considering layering overhead or the cost of converting an unbounded gate to binary fan-in. The unqualified assertion in `Hierarchy.lean` that the book's `SIZE(T)` “is `Language.InSIZE`” compounds the problem.

The same counterexample survives an eventual-bound interpretation of `SIZE(1)`: it occurs at every sufficiently large length. This is not just a repair of length zero. The useful preservation statement is about **polynomial-size existence**, allowing the polynomial budget to change.

**Repair:** Restrict the preservation claim to `P/poly`, explicitly label `InSIZE` as the finite, layered, unbounded-fan-in, non-input-node size class, and remove exact identification with the book's `SIZE(T)`. For later quantitative results, add the book's bounded-fan-in size predicate or state a simulation with its transformed budget. Do not transfer the hierarchy theorem at the same `T` merely because both definitions use the name `SIZE`.

### 4. MAJOR — the hard-function ledger does not justify its quantitative comparison with the DAG theorem

**Locations:** `HardFunctions.lean:33-60,247-249`; facade `TCSlib/Complexity/CircuitComplexity.lean:53-54`.

The ledger starts by saying the statements are incomparable, but then calls the book's conclusion strictly stronger using the informal bound “tree size $S$ gives DAG size at most $S+2n$.” Even granting that conversion, the **stated constants do not yield the claimed implication**. At $n=20$, the two integer cutoffs are

$$
\left\lfloor\frac{2^{20}}{10\cdot20}\right\rfloor=5242,
\qquad
\left\lfloor\frac{2^{20}}{20+5}\right\rfloor=41943.
$$

The quoted conversion transfers hardness at DAG cutoff 5242 only to tree cutoff

$$
5242-2\cdot20=5202,
$$

not to 41943. Conversely, tree hardness alone does not rule out small DAGs with sharing. The phrase that no bound runs the other way is also literally too strong: finite DAGs can be unrolled with a depth-dependent bound; a polynomial comparison is what is unavailable here.

This does not dispute that the book treats the more general computational model, or the common exponential asymptotic order. It disputes a comparison between the two **specific quantified bounds** on the strength of the stated conversion. The facade then drops the tree qualification altogether while attaching the book's theorem number to the different cutoff.

**Repair:** Retain the explicit tree-variant disclaimer; distinguish model generality from numerical implication; state only the transferred cutoff actually justified. Replace the unqualified reverse-bound claim with the absence of a suitable polynomial simulation. In the facade write “tree-circuit analogue of Theorem 6.21,” including the local cutoff. A DAG counting theorem is a separate deliverable, not established by this file.

### 5. MINOR — additional graph and nullary-gate conventions need an explicit ledger entry

**Locations:** `FeedForward.lean:45-56,108-115`; `PPoly.lean:36-46`; `Basic.lean:107-109,129-132,160-168`; `UnaryLanguages.lean:29-33`; `SizeClasses.lean:25-31`; catalog `TCSlib/ComputationalModels.lean:39-41`.

A singleton designated output type does not say that the underlying graph has only one sink: earlier-layer nodes may be unused. Inputs may also be unused. `Gate.inputs` need not be injective, so repeated wires are permitted. Finally, `stdGateOps` includes `andGateOp 0`, a constant-one operation; trees admit both nullary constants. An empty tree gate is assigned depth one despite having no input-to-output path.

The zero-length behavior is described in several places, but the graph conventions are not collected as differences from the baseline. The sentence that `stdGateOps` has no constant gate is literally misleading: it lacks a separately named constant constructor, not a constant operation.

**Repair:** Add these conventions to the model ledger, including the intended $n=0$ extension. Say that false is implemented as NOT of nullary AND. The catalog should also say that `stdGateOps` is an optional restriction for the Boolean specialization: raw `FeedForward` does not enforce a basis. Explain that duplicate predecessors can be removed using AND idempotence and irrelevant nodes can be discarded when comparing computational power; exact size/depth accounting remains model-specific. No requirement to forbid these harmless representations is imposed.

### 6. MINOR — missing implementations are described as intrinsic representation obstacles

**Locations:** `CircuitSat.lean:39-49`; `Encoding.lean:43-50`; related wording at `Hierarchy.lean:49-53`.

The claim that the tree representation is forced because feedforward nodes are arbitrary types with nothing to index Tseitin variables by is incorrect. A dependent sum of layer/node types supplies exactly such an index; `FeedForward.size` itself already uses a dependent sum. An identity gate and a NOT gate each admit two binary Tseitin clauses without any detour through `Circuit`.

Similarly, a finite tree can be numbered by preorder and represented by an adjacency matrix. What is missing is the implementation and its cost bounds. The absence of an explicit identity constructor in `Circuit` is not a semantic obstruction either: a singleton AND represents identity. NOT requires a complementary-tree transformation rather than an AND/OR label in the existing unroller.

**Repair:** Replace assertions that the model forces or prevents an encoding with precise statements that the relevant indexing, gate cases, normalization, and executable maps have not been implemented. Preserve the valid warning that no current polynomial-time bridge is established. Do not interpret the infinite ambient variable type as a proof of unencodability: each output formula has finite support.

### 7. MINOR — machine-model and `P` availability comments are stale within this very bundle

**Locations:** `CircuitSat.lean:30-31`; `Encoding.lean:34-36`; facade `TCSlib/Complexity/CircuitComplexity.lean:43-45`. Contradicting current descriptions: `SizeClasses.lean:33-39`, `UHalt.lean:35-40`, and `TCSlib/ComputationalModels.lean:49-55`.

The former comments say TCSlib has no machine model or no `P`; the latter explicitly say both now exist on this branch. The missing items are connecting theorems and reduction implementations, not the ability to state `P`.

**Repair:** Use the same current explanation everywhere: the campaign machine/class infrastructure exists; these modules do not yet provide the required simulations or polynomial-time reduction. This is a prose correction, not a request to reopen closed gates.

### 8. MINOR — upper bounds are narrated as exact values

**Locations:** `UnaryLanguages.lean:42-44,149-150,174-176`; `Parity.lean:28-37,216-220,311,329-341`.

`unaryFamily` has size **at most** two, not two at every length. Taking the all-ones language makes every branch `allOnesCircuit`, whose size is one. Similarly, the displayed $2\lceil\log_2 n\rceil+2$ for the parity construction is an upper bound, not its depth: at $n=1$, `parityCircuit` is a literal with depth zero, whereas that expression is two. At $n=0$, it is an empty OR of depth one.

**Repair:** Replace the exact-value wording with “at most” or a displayed inequality. The formal bounds, parity semantics, and `parity_inNC_one` need no repair.

### 9. MINOR — “collapse the hierarchies” overstates what `NC_eq_AC` says

**Location:** `NCAC.lean:520-522`; context `NCAC.lean:143-159,512-517`.

The theorem identifies the **unions** of the tree classes. Its two premises compare equal indices in one direction and successive indices in the other. They do not establish equality at each index or collapse levels to a fixed level. The facade's explicit union reading is better than the theorem docstring.

**Repair:** Say “the unions coincide.” Keep the tree-model qualifier visible on public class documentation. This finding does not allege that the formal equality is false.

### 10. MINOR — book section/type mappings contain errors

**Locations:** pack `ch6-circuits-bundle.md:16-18`; `Hierarchy.lean:311-312`; `Universal.lean:55-56`.

Theorem 6.22 is in **§6.6**, not §6.5. The ranges called “Defs 6.1-6.5” and “Defs 6.9-6.14” mix definitions with examples, a note, lemmas, and a theorem. More substantively, the assertion that length three is where “[AB09, Thm 6.21]” first has content refers to the local tree result: the book cutoff there is (8/30<1), whereas the local cutoff is one. Finally, the sharper universal upper bound is **Exercise 6.1**; write “Exercise” rather than the otherwise example-like `Ex 6.1` abbreviation.

**Repair:** Correct the source map and use “the local tree counting bound” in the length-three docstring. Record pack corrections in the resolutions file, keeping the sent pack immutable.

### 11. MINOR — the attached sweep list has 22 modules, not the attested 23

**Locations:** pack `ch6-circuits-bundle.md:63-66`; `scripts/circuit_module_order.txt:1-22`.

The attached list has 22 nonblank entries. This contradicts the claimed size of that very list. It does not demonstrate a missing elaboration or undermine the separately accepted kernel-check premise.

**Repair:** Reconcile the claimed sweep with the actual list: supply the omitted entry if one was checked, or correct the count and identify the corresponding log in the resolutions record. No fresh proof audit is requested.

### 12. NOTE — interface preview: target the guarded family directly for `P ⊆ P/poly`

**Locations:** `PPoly.lean:69-82,95-121`; `FeedForward.lean:51-56,112-115,288-307`; `SizeClasses.lean:33-39`.

The destination is well-formed: a finite family, one fixed polynomial bound, standard basis, and exact language equality. Construct a finite-layer simulation of the campaign machine, exposing its gate-basis proof and alphabet transport. Do not use finding 1's wrapper to obtain a spurious small simulation.

`GateOp` contains a type and a function rather than a finite operation tag. For an executable bridge, a tagged gate syntax with a proved interpretation into `stdGateOps` would simplify circuit construction and later serialization. This is an interface suggestion, not a present defect in nonuniform `P/poly`.

**Proposed follow-up:** Specify the simulation's evaluation, finiteness, basis and size contracts before its implementation; make finite-length handling explicit. No changes to the trusted machine definitions are needed merely to state the inclusion.

### 13. NOTE — interface preview: tree CKT-SAT needs an appropriate NP-hardness route and a total string map

**Locations:** `CircuitSat.lean:39-53,73-79,99-131`; `Encoding.lean:230-301`; `FeedForward.lean:245-273`; catalog carrier distinction at `TCSlib/ComputationalModels.lean:59-66`.

The current target is **formula/tree satisfiability**, which can serve as an NP-hard language. However, unrolling an arbitrary machine-simulation DAG is not a justified polynomial-size reduction. A direct route from the campaign's already formalized SAT/3SAT carrier to an AND-of-ORs `Circuit` avoids that problem. Another route is a finite DAG Tseitin construction followed by such a tree.

The campaign carrier `Std.Sat.CNF ℕ` and the legacy `NPReductions.CNFFormula` carrier are different interfaces. Also, reductions between languages must be total on bit strings. For a source decoder returning `none`, choose a fixed rejecting target string, e.g. `encodeSigma ⟨0, .node false []⟩` when the target is `cktSatLang`. The canonical-string characterization supplies the semantic specification; it is not a running-time theorem.

**Proposed follow-up:** Pin the actual source/target languages and encodings; implement a syntax-directed map, a malformed-input branch, both membership directions, and its machine-level time bound. Maintain the distinction between NP-hardness and the separate direction to 3SAT.

### 14. NOTE — interface preview: clause counts and unary indices need bit-length accounting

**Locations:** `Encoding.lean:34-57,84-105,230-232,431-432`; `CircuitSat.lean:99-102`.

The 13-times-input-length theorem counts clauses, not variable identifiers or output bits. For a concrete reduction, number the finitely many occurring variables/subcircuits and encode those numbers. This can use finite support despite the infinite ambient variable type. When reducing from a formula whose variable names are binary naturals, first rename occurring variables densely: expanding an identifier $2^k$ directly into a unary circuit index would cost at least $2^k$ bits despite its $k+1$-bit input name. Unary-index inflation is harmless only relative to an already polynomially bounded arity/index range.

**Proposed follow-up:** Add dense variable numbering, finite-string output encoding and cost bounds before claiming a polynomial-time reduction. These are advisory obligations, not reasons to reject the present equisatisfiability statement.

### 15. NOTE — interface preview: `UHALT` uses a separate computability framework

**Locations:** `UHalt.lean:25-40,90-101`.

The accepted Mathlib result in `UHalt` is a statement about `ComputablePred`. Combining it with the campaign's `P` to conclude a strict inclusion requires the appropriate implication from campaign decidability to Mathlib computability. This is additional to `P ⊆ P/poly`; it is not present merely because both use `Language Bool`.

**Proposed follow-up:** If the subsequent goal includes `P ⊊ P/poly`, separately expose the computability-framework bridge. This is an advisory obligation, not a defect in the current `ComputablePred` statement.

## 3. Seeded attack results and quantitative checks

These are checks of meanings and construction parameters, not re-audits of the kernel-checked proofs.

| Attack surface | Result and evidence |
|---|---|
| Arbitrary operation as one gate | **Guarded in every class.** `InSIZE` requires `OnlyUsesGates stdGateOps` (`PPoly.lean:109-111`); `InPPoly` factors through it; `inPPoly_iff` retains it. `InNC`, `InAC` and `InTreeSize` quantify over the AND/OR/literal inductive syntax (`NCAC.lean:131-138`; `Hierarchy.lean:181-183`). `TreeSize` has no extra gate predicate because it needs none. Finding 1 is a conversion-description defect, not an escape from these guards. |
| Infinite layers / `Nat.card` | **Guarded.** `CircuitFamily.finite` covers every layer at every length (`PPoly.lean:69-73`). The non-input sigma in `FeedForward.size` is consequently finite. Standard operations also have finite arity; an infinite gate-input type cannot enter the guarded class. `HardFunctions` counts a subset of the finite Boolean-function type, so its `.ncard` has no analogous infinite-carrier trap. |
| Malformed/noncanonical words | **Pass in both directions.** `decodeSigma_encodeSigma` and `encodeSigma_of_decodeSigma` give `decodeSigma w = some C` iff `encodeSigma C = w` (`Encoding.lean:244-255`). Hence decode-to-`none` is exactly failure to be any canonical encoding. `mem_cktSatLang_iff_exists` additionally requires the encoded circuit to be satisfiable (`Encoding.lean:299-301`). Canonical unsatisfiable words are rejected too. |
| Acceptance orientation | **Pass.** `Accepts` maps `Bool` inputs through `finTwoEquiv.symm` and requires output `1` (`PPoly.lean:79-92`). The characterization at `SizeClasses.lean:62-65` identifies exactly `true`; `prod_fin_two_eq_one_iff` identifies AND; `notGateOp` exchanges the two values (`UnaryLanguages.lean:96-100`). Tree acceptance requires `true` directly. |
| Quantifier placement | **Pass.** One family is chosen before all input lengths/words, and coefficients/exponents precede `∀ n`. Set equality enforces both acceptance directions. `InTreeSize`'s pointwise iff has the same force because every assignment is represented by a list (`Hierarchy.lean:181-183,211-216`). Noncomputable choice of a family is intentional nonuniformity. |
| Polynomial/logarithmic repairs | **Pass for asymptotic classes.** A fixed factor and finitely many short lengths can be absorbed in global constants. For $n\ge2$, $n+1\le2n$ and $\lfloor\log_2 n\rfloor+1\le2\log_2 n$. This does not preserve a fixed exact size budget: finding 3. |
| Nullary and empty-word cases | **Pass under the local conventions.** Empty AND is true; empty OR is false (`Basic.lean:129-132`). The empty word belongs to `allOnes` (`SizeClasses.lean:68`), and belongs to `unary S` exactly when $0\in S$. `parityCircuit 0` is false (`Parity.lean:359-360`). The encoded zero-input true circuit is `[false,true,true,false]`; the empty bit string is malformed (`Encoding.lean:311-330`). |
| Depth exponent zero and unions | **Pass.** `HasPolylogDepth 0` is exactly a uniform constant depth bound, since the positive base is raised to zero (`NCAC.lean:121-123`). `NC` uses indices at least one and `AC` includes zero (`NCAC.lean:148-159`). The inclusion into successor levels supports the union equality; it does not assert levelwise equality. |
| Nonempty hierarchy witness | **Pass for the advertised concrete instance.** `zero_mem_treeSize_one` uses constant false with size one (`Hierarchy.lean:191-196,313-319`). The general hierarchy theorem permits empty lower classes if any `T n = 0`; its hypotheses do not assert nonemptiness. The discussion of `ℓ n₀ ≥ 3` addresses only the distinguished-length obstruction, not all lengths. |
| Truth-table universality | **Pass.** `universalCircuit_eval` quantifies over every function and assignment, including arity zero. Attainment at constant true concerns this construction's size, not minimum circuit complexity (`Universal.lean:124-169`). |

For explicit counting, let $S=C.\mathrm{size}$, let $r=C.\mathrm{litCount}$, and let $m=\lvert \mathrm{encodeSigma}\langle n,C\rangle\rvert $. A tree has $S-r$ internal gates and $S-1$ child edges, counting nullary gates as internal nodes. The following arithmetic follows directly from the constructors and clarifies what each bound measures:

| Claimed bound | Meaning/check |
|---|---|
| $2^{(n+4)S}$ computable functions | Each literal contributes `idx + 3` encoding bits; each internal node contributes three bits plus one per child. Thus $ \lvert \mathrm{encodeCircuit}(C)\rvert +1=4S+\sum_{\text{literal occurrences}}\mathrm{idx}\le(n+4)S$. Fewer-than-$(n+4)S$-bit strings number at most $2^{(n+4)S}$. The round trip makes the circuit encoding injective. This is a tree count, not a DAG count. `HardFunctions.lean:141-190`. |
| $3S$ intermediate clauses | Leaf clauses contribute $2r$; gate clauses contribute $(S-1)+(S-r)$; the output contributes one. Total $2r+(S-1)+(S-r)+1=2S+r\le3S$. `CircuitSat.lean:113-131,379-404`. |
| $7S$ intermediate literal occurrences | Leaves contribute $4r$; gate clauses contribute $3(S-1)+(S-r)$; the output contributes one. Total $4S+3r-2\le7S$. `Encoding.lean:371-418`. |
| $13m$ final clauses | The exported bound is exactly on `(to3SAT ...).length`, and $S\le m$. Its composition uses the accepted legacy `SATTo3SAT.length_to3SAT_le` estimate with the clause/occurrence budgets; the numerical coefficient is $2\cdot3+7=13$. The legacy transformation is imported trusted context, not an independently audited attachment. No bit-length or time interpretation follows. `Encoding.lean:431-437`. |
| $32(n+1)^4$ parity size | For $n\ge1$, fan-in at most two and depth at most $4(\lfloor\log_2 n\rfloor+1)$ give $S+1\le2^{4(\lfloor\log_2 n\rfloor+1)+1}=32(2^{\lfloor\log_2 n\rfloor})^4\le32(n+1)^4$. At $n=0$, the circuit has size $1\le32$. `Basic.lean:290-292`; `Parity.lean:321-341`. |
| $2^n(n+1)+1$ universal size | One top OR plus $n+1$ nodes per satisfying assignment. There are at most $2^n$ assignments, with equality for constant true. At arity zero, the false construction has size one and the true construction size two. `Universal.lean:95-122,137-169`. |

The unary encoding makes an upper bound expressed in encoded length weaker, never a stronger bound in a shorter representation. `Encoding.lean:55-57` should use “does not invalidate this upper bound” rather than implying inflation does not weaken it. The separate input-arity prefix is $n+1$ bits, so a satisfying assignment of length $n$ is also bounded by the encoded input length. This is helpful for a future NP-membership interface, without itself proving one.

## 4. Divergence-ledger coverage by module

| Module | Audit outcome |
|---|---|
| `Basic` | Tree syntax and literal polarity are clear. Missing layered-normal-form and metric distinctions are major: finding 2. Nullary conventions should be collected: finding 5. |
| `CircuitSat` | Equisatisfiability, structural sharing of equal subcircuits, tree input, unbounded clause width, and infinite ambient variables are disclosed. No implication from clause count to polynomial time is asserted. Repair the stated implementation obstacles and stale machine claim: findings 6-7. |
| `Encoding` | Canonical-image semantics and rejection are correct. Tree representation, unary indices, and absence of output bit/time bounds are disclosed. Correct the representation rationale and qualify future encoding-cost claims: finding 6 and note 14. |
| `FeedForward` | Generic operations, size and finiteness have the stated meanings. The tree wrapper's description and resource prose are materially wrong: finding 1. The AND/OR unroller's evaluation theorem does include its required `IsAndOrGate` hypothesis; it is not a general `stdGateOps` conversion. |
| `HardFunctions` | Counting result is correctly typed over trees and uses the stated cutoff. The model difference is disclosed, but its quantitative comparison and facade presentation require finding 4's repair. |
| `Hierarchy` | Tree class, padding parameters, one-length separation and nonidentity with the book theorem are disclosed. No independent gate-smuggling or quantifier issue. Repair exact identification of the other local `SIZE` with the book's class, and the length-three attribution: findings 3 and 10. |
| `NCAC` | Fan-out restriction, lack of an established DAG comparison, free literal negation, logarithmic repair and nonuniformity are disclosed. The level/union formulas are correct. “Unions coincide” is the appropriate prose: finding 9. |
| `PPoly` | Finiteness and gate guards are adequate. The polynomial union has the intended nonuniform reading. Fixed-size preservation and the remaining graph conventions need findings 3 and 5. |
| `Parity` | Odd parity, empty input, dual-pair construction and the actual resource inequalities match. Correct only the exact-depth prose: finding 8. |
| `SizeClasses` | Monotonicity, the polynomial-budget implication, all-ones semantics and constant-size local implementation match. Its explicit fan-in/counting divergence is useful evidence for finding 3. |
| `UnaryLanguages` | Unary restriction is genuine; arbitrary per-length choice is intentional and both branches use the basis. Correct the constant-operation and exact-size wording: findings 5 and 8. |
| `UHalt` | Numbering change and Mathlib computability interpretation are disclosed. The statements do not already claim campaign-machine undecidability or `P ⊊ P/poly`; note 15 identifies the future bridge. |
| `Universal` | DNF/CNF duality, local size convention and construction-specific attainment are disclosed. No optimal $O(2^n/n)$ result is claimed. Correct the exercise label: finding 10. |
| Facade | The union reading and hierarchy disclaimer are good. Propagate the tree qualifier on hardness and update `P` availability: findings 4 and 7. |

## 5. Closure and source record

For this round, resolve findings **1-4** before closing the gate. Accurate renaming, restricted claims and complete divergence ledgers are valid repairs where a stronger bridge or theorem is deliberately deferred. Findings **12-15** are advisory and do not add present implementation requirements. In particular, this audit does not require proving the DAG hierarchy, replacing the tree `NC`/`AC` track, or formalizing polynomial-time reductions to close a semantic audit of the disclosed variants.

Book sources consulted:

- **AB09:** Sanjeev Arora and Boaz Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009. Published Chapter 6, pp.106-122. [Publisher record](https://www.cambridge.org/core/books/abs/computational-complexity/boolean-circuits/F05D6A6727AD15138220D1C5BC22AEAE); [consulted scan of the published book](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora%2C_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press%282009%29.pdf). Printed p.116 was visually checked to confirm the hierarchy statement and section number. The older Princeton draft was not used to assign published item numbers.
- **OD14:** Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014. Definitions 4.26-4.27, pp.103-104, checked in the [author's corrected edition posted in 2021](https://arxiv.org/pdf/2105.10386); these pages were visually checked. This is the consulted edition, not an assertion that a byte-identical 2014 first-printing PDF was supplied. Review was limited to the attributed substrate conventions, not the excluded Switching/LMN development.

The explicit counterexamples and construction counts above are semantic deductions from the supplied definitions. Small evaluations/arithmetic were checked independently; no Lean theorem was refuted or its proof re-audited. The imported legacy 3SAT facts and repository-side elaboration/axiom attestations remain the stipulated trusted premises.

**Notation glossary:** $n$: input length; $x$: Boolean input; $C,C_n$: circuit and length-indexed circuits; $f$: Boolean function; $L$: language; $T,T'$: size-bound functions; $a,k$: global polynomial coefficient and exponent; $d,i$: depth exponent or class index; $n_0$: distinguished input length; $\ell$: padding-length function; $S$: tree node count, or the set of unary lengths when writing `unary S`; $r$: literal-occurrence count; $m$: arity-tagged encoding length; $c$: a normal-form circuit in finding 2 or the polynomial exponent in the book's union; `idx`: a literal's zero-based variable index; $\langle C\rangle$: a circuit encoding; `size`/`depth`: the indicated model's own measures, not interchangeable across carriers.

## ===== audits/ch6-circuits-resolutions.md =====

# Chapter-6 circuit surface — audit loop resolutions (OPEN, round 2 pending)

Protocol: `workflow.md` §3. Round 1: pack `audits/ch6-circuits-pack.md`
(commit `05971a42`, auditing `28690c01`), findings
`audits/ch6-circuits-findings.md` — **0 blockers, 4 majors, 7 minors,
4 notes**; gate open. The findings file is preserved verbatim; the sent
pack is immutable, and its errata are acknowledged below. All fifteen
findings were **accepted in full** after source verification; no finding
was contested. Repairs are prose/ledger/docstring only — **zero Lean
statements changed** — as §5 of the findings expressly permits for
deliberately deferred bridges.

## Round-1 repairs (findings 1–11)

| # | Sev. | Repair |
|---|---|---|
| 1 | major | `FeedForward.lean`: `Circuit.toFeedForward` re-described as a **semantic wrapper** (single unrestricted `⟨Fin n, C.eval⟩` gate + identity wires; `size = depth = C.depth + 1`; never discharges `OnlyUsesGates`; only evaluation preserved) in the declaration docstring, the module docstring, and the section header; the false `C.size * C.depth` prose bound removed. Catalog entry rewritten to match. `Hierarchy.lean`'s already-accurate disclosure untouched. |
| 2 | major | `Basic.lean`: divergence ledger rewritten — the normal forms are *alternating trees over base clauses*, not [OD14, Def 4.26]'s layered circuits (no common input layer, unequal literal paths); the three size/depth measures declared non-interchangeable with the clause-of-two-literals example (normal-form size 1 / depth 0 vs `toCircuit` size 3 / depth 1), the root-counting convention, and the `.node []`/`.clause []` depth asymmetry; the mutual-block header de-attributed from Def 4.26. |
| 3 | major | `PPoly.lean`: "All are class-preserving" restricted to the polynomial union, with the auditor's own counterexample (`allOnes ∈ InSIZE (fun _ => 1)` vs no size-1 circuit in AB's input-counting model for n ≥ 2) recorded in the ledger; `InSIZE` labeled as this model's size class with transfer requiring an explicit simulation. `Hierarchy.lean`: "Def 6.2's `SIZE(T)` **is** `InSIZE`" weakened to "is rendered, with declared divergences — not the same fixed class". Facade `SizeClasses` bullet likewise. |
| 4 | major | `HardFunctions.lean`: the "strictly the stronger" comparison replaced by the precise statement — neither quantified bound implies the other on the strength of the `S + 2n` conversion, with the auditor's n = 20 instance (5242 → 5202 ≪ 41943) in the ledger; "no bound runs the other way" corrected to "no polynomial bound" (depth-exponential unrolling exists). Facade bullet now reads "the tree-circuit analogue of [AB09, Thm 6.21] … no **tree** circuit". |
| 5 | minor | `PPoly.lean` ledger: graph conventions collected (unused nodes/inputs permitted; `Gate.inputs` not injective; `andGateOp 0` is a constant-**one** operation; no primitive constant-false). `Basic.lean` ledger: empty AND/OR value/size/depth conventions. `UnaryLanguages.lean`: "no constant gate" corrected to "no primitive constant-false". Catalog: `FeedForward` entry says the raw model enforces no basis; classes impose `stdGateOps` via `OnlyUsesGates`. |
| 6 | minor | `CircuitSat.lean`: "the tree is forced" → "the chosen carrier"; the FeedForward Tseitin map described as **unimplemented, not impossible** (binary clauses for `id`/`NOT`; the layer/node dependent sum as a variable index). `Encoding.lean`: the adjacency-matrix representation described as not implemented (preorder numbering possible), not unavailable. |
| 7 | minor | Stale "TCSlib has no machine model / no `P`" corrected at the three sites round 1 found (`CircuitSat.lean`, `Encoding.lean`, facade `UHalt` bullet), aligned with the earlier N5 wording: the machine model and `P` live on this branch; the missing items are the simulations/reductions, tracked in `backlog.md` §3. |
| 8 | minor | `UnaryLanguages.lean`: "size 2 at every length" → "at most 2 (1 on the all-ones branch)". `Parity.lean`: the `2⌈log₂ n⌉ + 2` depth narrated as an upper bound (with the n = 1 depth-0 literal noted), in the ledger and the `xorFuel_depth` docstring. |
| 9 | minor | `NCAC.lean`: `NC_eq_AC` docstring now says the **unions** coincide, no levelwise equality asserted. |
| 10 | minor | `Hierarchy.lean`: the length-3 remark re-attributed to the local tree counting bound, not [AB09, Thm 6.21]. `Universal.lean`: "Ex 6.1" → "Exercise 6.1". Pack-side errors acknowledged as pack errata below. |
| 11 | minor | Attestation discrepancy acknowledged as pack erratum below; the sweep list and its counts reconciled there. |

## Round-1 recordings (notes 12–15)

All four advisory notes are recorded as inherited interface guidance in
`backlog.md` §3 (gate-by-gate family construction against
`OnlyUsesGates stdGateOps`; the CKT-SAT reduction route from the audited
`Std.Sat.CNF ℕ` carrier with a total string map and fixed rejecting word;
dense variable renumbering before unary indices; the
campaign-decidability → `ComputablePred` bridge for `P ⊊ P/poly`). No
implementation obligation attaches to this round.

## Pack errata (round-1 pack, immutable as sent)

1. **Finding 10 (sources).** The pack placed Theorem 6.22 in "§6.5"; it is
   in **§6.6** of the published 2009 edition. The ranges "Defs 6.1–6.5"
   and "Defs 6.9–6.14" mix definitions with examples, a lemma, and a
   theorem; read them as section ranges, not definition lists.
2. **Finding 11 (sweep-list count).** The pack attested "the 23-module
   circuit list"; the attached `scripts/circuit_module_order.txt` has
   **22** entries. The count was stale: the list had 23 entries until
   `DecisionTree` was relocated out of the tree (commit `193470a3`,
   which removed its line) shortly before the pack was written. The
   verification of record for the audited commit is the 39-module batch
   sweep over the current 22-entry list plus the Switching/LMN reverse
   dependencies and the catalog (zero errors), re-run after this round's
   repairs.

## Round 2

Round-2 pack: `audits/ch6-circuits-reaudit-pack.md`. Scope: verify that
each repair discharges its finding; re-issue the task-1 verdicts for
[AB09] Defs 6.1 and 6.2 (the two *divergent-undeclared* rows) and the
Thm 6.21 row; sweep the minor repairs; confirm the notes' recording.
Gate closes on zero blockers/majors.

## ===== TCSlib/Complexity/CircuitComplexity.lean =====

/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang, Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.Basic
import TCSlib.Complexity.CircuitComplexity.Formulas
import TCSlib.Complexity.CircuitComplexity.FeedForward
import TCSlib.Complexity.CircuitComplexity.PPoly
import TCSlib.Complexity.CircuitComplexity.CircuitSat
import TCSlib.Complexity.CircuitComplexity.Encoding
import TCSlib.Complexity.CircuitComplexity.Universal
import TCSlib.Complexity.CircuitComplexity.HardFunctions
import TCSlib.Complexity.CircuitComplexity.NCAC
import TCSlib.Complexity.CircuitComplexity.Parity
import TCSlib.Complexity.CircuitComplexity.Hierarchy
import TCSlib.Complexity.CircuitComplexity.UnaryLanguages
import TCSlib.Complexity.CircuitComplexity.UHalt
import TCSlib.Complexity.CircuitComplexity.SizeClasses

/-!
# Circuit Complexity

Boolean circuits and formulas, the class `P/poly`, and Arora–Barak §6.1.

## Contents

- `CircuitComplexity.Basic`: `BoolCircuit.Lit`, the general circuit tree
  `BoolCircuit.Circuit` (unbounded fan-in) with `eval` / `litCount` / `depth` /
  `size` / `maxFanin`, and the alternating normal forms
  `NAndCircuit` / `NOrCircuit` with `toNAnd` / `toNOr` and the forgetful map
  `toCircuit`.
- `CircuitComplexity.Formulas`: `Literal`, `Term`, `DNF`, `CNF` with `eval`
  and `width`.
- `CircuitComplexity.PPoly`: the class `P/poly` of languages decided by
  polynomial-size non-uniform circuit families, over the `FeedForward` model.
- `CircuitComplexity.CircuitSat`: CKT-SAT ([AB09, Def 6.9]) and the Tseitin reduction
  to 3SAT ([AB09, Lem 6.11], equisatisfiability only), composed with
  `NPReductions.SATTo3SAT` to land in genuine 3-CNF.
- `CircuitComplexity.UnaryLanguages`: [AB09, Claim 6.8] — every unary
  language is in `P/poly`, via [AB09, Ex 6.3]'s AND circuit and a constant-`0`
  circuit built from the gate set.
- `CircuitComplexity.UHalt`: [AB09, p.110] — `UHALT`, an undecidable unary language,
  hence a language in `P/poly` that is not computable. `P ⊊ P/poly` itself is not
  stated: the bridge from the campaign's `P` to `P/poly` ([AB09, Thm 6.6]) and
  the computability-framework bridge are both deferred (`backlog.md` §3).
- `CircuitComplexity.Encoding`: a bit-string encoding of `BoolCircuit.Circuit` as a
  `Computability.FinEncoding`, CKT-SAT as a genuine `Language Bool`
  ([AB09, Def 6.9]), and the output-size half of [AB09, Lem 6.11] — clause count
  only, not `≤p`.
- `CircuitComplexity.Universal`: [AB09, Claim 2.13] — every Boolean function on
  `n` bits is computed by a circuit of size at most `2 ^ n * (n + 1) + 1`, via
  the DNF over its satisfying assignments.
- `CircuitComplexity.HardFunctions`: the tree-circuit analogue of [AB09, Thm 6.21]
  — some Boolean function on `n` bits is computed by no **tree** circuit of size
  `2 ^ n / (n + 5)`, by counting over the tree encoding.
- `CircuitComplexity.NCAC`: [AB09, Defs 6.24–6.25] — the classes `NC^d` / `AC^d`
  and their unions, and the inclusions `NC^i ⊆ AC^i ⊆ NC^{i+1}` and hence
  `NC = AC`. Over the tree-shaped `BoolCircuit.Circuit`, not the `FeedForward`
  model of `PPoly.lean`.
- `CircuitComplexity.Parity`: [AB09, Ex 6.26] — `PARITY ∈ NC¹`, by the balanced
  binary tree, built as dual pairs because `Circuit` negates only at literals.
- `CircuitComplexity.Hierarchy`: a nonuniform size hierarchy over the tree-shaped
  `BoolCircuit.Circuit`, from [AB09, Claim 2.13] and [AB09, Thm 6.21] by padding.
  **Not** [AB09, Thm 6.22]: its class is not `Language.InSIZE`.
- `CircuitComplexity.SizeClasses`: monotonicity of the model's size classes
  (`Language.InSIZE` — not [AB09, Def 6.2]'s fixed `SIZE(T)`; see `PPoly.lean`'s
  ledger), the passage to `P/poly` for polynomially bounded budgets, and
  [AB09, Ex 6.3]
  — the all-ones language `{1ⁿ : n ∈ ℕ}` has linear-size circuits.

`Basic`, `Formulas` and `DecisionTree` are mutually independent; the bridge from
normal-form circuits to `DNF` / `CNF` lives in
`TCSlib.BooleanAnalysis.LMN.NormalFormConversion`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [OD14] R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University
  Press, 2014.
-/

## ===== TCSlib/Complexity/CircuitComplexity/Basic.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.List.Nodup
-- Not used below.  This file's base-clause invariant is a `List.Nodup`, that is a
-- `List.Pairwise`, and `LMN/NormalFormConversion.lean` (which imports this file
-- and `Formulas.lean`, nothing else) reads it back through `List.Pairwise.forall`.
-- Of the 46 modules that transitively import this file that is the only one
-- affected: without this import `lake build` fails there, at line 144, and
-- nowhere else.
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Boolean Circuits: Literals and Circuit Trees

## Main definitions

* `BoolCircuit.Lit` — a literal: an index `idx : Fin n` and a sign
  (`sign = true` is the positive literal).
* `BoolCircuit.Circuit` — a Boolean circuit tree, `lit` or `node isAnd children`,
  with `eval`, `litCount`, `depth`, `size`, `maxFanin` and the list-level `maxDepth`,
  `sumSize`, `maxFaninL`.  Fan-in is unbounded; a bound is imposed downstream as a
  hypothesis `c.maxFanin ≤ w`, never as structure.
* `BoolCircuit.NAndCircuit` / `NOrCircuit` — normal-form circuits, strictly
  alternating AND/OR with a `Nodup` variable-index invariant at the base clauses.
* `BoolCircuit.Circuit.toNAnd` / `toNOr` — normalization into that form;
  `NAndCircuit.toCircuit` / `NOrCircuit.toCircuit` — the forgetful map back.

## Main results

* `Circuit.eval_lit`, `Circuit.eval_node_true_iff`, `Circuit.eval_node_false_iff`
  — the semantics of a leaf and of an unbounded AND / OR gate.
* `Circuit.one_le_size`, `Circuit.maxFanin_le_size`, `Circuit.size_succ_le_two_pow` — a
  circuit has at least one node, a gate no more inputs than the circuit has nodes, and a
  fan-in-2 circuit's size is bounded by its depth.
* `Circuit.depth_node` / `size_node` / `maxFanin_node` and the `_nil` / `_cons` unfoldings.
* `toNAnd_eval` / `toNOr_eval`, `toNAnd_litCount` / `toNOr_litCount`,
  `toNAnd_size_le` / `toNOr_size_le` — normalization preserves semantics and
  literal count, and at most doubles the size.

## Divergences from [OD14, §4.5]

`NAndCircuit` / `NOrCircuit` are **alternating trees over base clauses**, not a
direct realization of [OD14, Def 4.26]'s layered circuits: alternation holds
between parent and child connectives, but there is no common input layer and no
requirement that root-to-literal paths have equal length (an `AND` root may hold
both an `OR` clause and an `OR` node over an `AND` clause).  [OD14, Def 4.27]'s
condition that no base gate reads a variable twice is the `Nodup` invariant.
The size/depth measures are **not interchangeable across the three carriers**:
`Circuit.size` counts every node, literal leaves included, where [OD14,
Def 4.27] counts only the internal layers; `NAndCircuit.size` / `NOrCircuit.size`
count clauses and nodes but not the literals inside a clause (a two-literal
clause has normal-form size `1` and `toCircuit` size `3`); normal-form `depth`
gives every base clause depth `0` where its `toCircuit` image has depth `1`;
and the root is counted in both sizes where [OD14] excludes the input and
output layers.  An empty `.node []` and an empty `.clause [] h` agree in value
and size but differ in normal-form depth (`1` vs `0`), so no uniform
depth-shift identity holds.  On `Circuit` itself, `.node true []` evaluates to
`true` and `.node false []` to `false` (the empty AND/OR), each with size `1`
and depth `1`.  No width measure is defined here — bottom-layer fan-in lives
on `DNF` / `CNF` in `Formulas.lean`.  `Circuit`, the unconstrained AND/OR tree,
matches no numbered definition: [OD14]'s circuits are DAGs.  `toNAnd` / `toNOr`
are this library's own normalization, each theorem naming its actual source and
target measures; their factor-2 size bound is proved here, not taken from
[OD14]'s `2 ^ d` remark.

## Provenance

`Circuit.one_le_size` was hoisted here from
`TCSlib/Complexity/CircuitComplexity/FeedForward.lean`, unchanged.

Split out of `TCSlib/BooleanAnalysis/Switching/Circuit.lean` (commit 94fd7c6),
which carried no copyright header; `Authors` above is that file's git author.
`DNF` / `CNF` live in `TCSlib.Complexity.CircuitComplexity.Formulas`, decision
trees in `...DecisionTree`, and the bridge from normal-form circuits to
`DNF` / `CNF` in `TCSlib.BooleanAnalysis.LMN.NormalFormConversion`.

## References

* [OD14] R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University
  Press, 2014.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : Nat}

-- ----------------------------------------------------------------
-- Section 1: Literals
-- ----------------------------------------------------------------

/-- A literal on `n` Boolean variables: a variable index together with a sign.
    `sign = true` means the positive literal xᵢ; `sign = false` means ¬xᵢ. -/
structure Lit (n : Nat) where
  idx : Fin n
  sign : Bool
deriving DecidableEq, Repr, Hashable

/-- Evaluate a literal under assignment `x`. -/
@[simp]
def Lit.eval (l : Lit n) (x : Fin n → Bool) : Bool :=
  if l.sign then x l.idx else !x l.idx

-- ----------------------------------------------------------------
-- Section 2: General (unconstrained) circuit
-- ----------------------------------------------------------------

/-- A Boolean circuit tree on `n` variables.
    - `lit l` is a single literal.
    - `node isAnd children` applies an AND gate (`isAnd = true`) or OR gate
      (`isAnd = false`) to its children.
    No alternation or deduplication constraint is imposed. -/
inductive Circuit (n : Nat) where
  | lit  : Lit n → Circuit n
  | node : (isAnd : Bool) → List (Circuit n) → Circuit n
deriving Repr

/-- Custom induction principle for `Circuit` that gives `∀ c ∈ cs, motive c` in the
    `node` case, working around the limitation that `induction` doesn't support
    nested inductives directly. -/
theorem Circuit.ind {n : Nat} {motive : Circuit n → Prop}
    (hlit : ∀ l, motive (.lit l))
    (hnode : ∀ isAnd cs, (∀ c ∈ cs, motive c) → motive (.node isAnd cs)) :
    ∀ c, motive c :=
  @Circuit.rec n motive (fun cs => ∀ c ∈ cs, motive c)
    hlit
    (fun isAnd cs ih => hnode isAnd cs ih)
    (fun _ h => nomatch h)
    (fun head tail ih_head ih_tail c hc => by
      cases hc with
      | head => exact ih_head
      | tail _ h => exact ih_tail c h)

/-- Evaluate a general circuit under assignment `x`. -/
def Circuit.eval : Circuit n → (Fin n → Bool) → Bool
  | .lit l, x => l.eval x
  | .node true cs, x  => cs.foldr (fun c acc => c.eval x && acc) true
  | .node false cs, x => cs.foldr (fun c acc => c.eval x || acc) false

/-- A leaf evaluates to its literal. -/
theorem Circuit.eval_lit {n : Nat} (l : Lit n) (x : Fin n → Bool) :
    (Circuit.lit l).eval x = l.eval x := by
  simp [Circuit.eval]

/-- An unbounded `AND` gate is true exactly when every child is. -/
theorem Circuit.eval_node_true_iff {n : Nat} (cs : List (Circuit n)) (x : Fin n → Bool) :
    (Circuit.node true cs).eval x = true ↔ ∀ c ∈ cs, c.eval x = true := by
  simp only [Circuit.eval]
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih]

/-- An unbounded `OR` gate is true exactly when some child is. -/
theorem Circuit.eval_node_false_iff {n : Nat} (cs : List (Circuit n)) (x : Fin n → Bool) :
    (Circuit.node false cs).eval x = true ↔ ∃ c ∈ cs, c.eval x = true := by
  simp only [Circuit.eval]
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih]

/-- Number of literal occurrences in a circuit. -/
def Circuit.litCount : Circuit n → Nat
  | .lit _ => 1
  | .node _ cs => cs.foldr (fun c acc => c.litCount + acc) 0

/-- Depth of a circuit (longest root-to-leaf path). -/
def Circuit.depth : Circuit n → Nat
  | .lit _ => 0
  | .node _ cs => 1 + cs.foldr (fun c acc => max c.depth acc) 0

/-- Total number of nodes (internal gates + literal leaves). -/
def Circuit.size : Circuit n → Nat
  | .lit _ => 1
  | .node _ cs => 1 + cs.foldr (fun c acc => c.size + acc) 0

/-- Maximum depth over a list of circuits (used in depth of a node). -/
def Circuit.maxDepth {n : Nat} (cs : List (Circuit n)) : Nat :=
  cs.foldr (fun c acc => max c.depth acc) 0

/-- Sum of sizes over a list of circuits (used in size of a node). -/
def Circuit.sumSize {n : Nat} (cs : List (Circuit n)) : Nat :=
  cs.foldr (fun c acc => c.size + acc) 0

/-- Maximum fanin of a circuit: maximum number of children of any gate, recursively. -/
def Circuit.maxFanin : Circuit n → Nat
  | .lit _ => 0
  | .node _ cs => max cs.length (cs.foldr (fun c acc => max c.maxFanin acc) 0)

-- ----------------------------------------------------------------
-- Section 2b: Size, depth and fan-in arithmetic
-- ----------------------------------------------------------------

/-- Every circuit has at least one node. -/
theorem Circuit.one_le_size (c : Circuit n) : 1 ≤ c.size := by
  cases c with
  | lit l => simp [Circuit.size]
  | node isAnd cs => simp [Circuit.size]

/-- Maximum fan-in over a list of circuits. -/
def Circuit.maxFaninL (cs : List (Circuit n)) : ℕ :=
  cs.foldr (fun c acc => max c.maxFanin acc) 0

/-- A gate's depth is one more than its children's. -/
theorem Circuit.depth_node (b : Bool) (cs : List (Circuit n)) :
    (Circuit.node b cs).depth = 1 + Circuit.maxDepth cs := by
  simp [Circuit.depth, Circuit.maxDepth]

/-- A gate's size is one more than its children's total. -/
theorem Circuit.size_node (b : Bool) (cs : List (Circuit n)) :
    (Circuit.node b cs).size = 1 + Circuit.sumSize cs := by
  simp [Circuit.size, Circuit.sumSize]

/-- A gate's fan-in is its arity or its children's fan-in, whichever is larger. -/
theorem Circuit.maxFanin_node (b : Bool) (cs : List (Circuit n)) :
    (Circuit.node b cs).maxFanin = max cs.length (Circuit.maxFaninL cs) := by
  simp [Circuit.maxFanin, Circuit.maxFaninL]

/-- `maxDepth` of the empty list. -/
theorem Circuit.maxDepth_nil : Circuit.maxDepth ([] : List (Circuit n)) = 0 := rfl

/-- `maxDepth` on a cons cell. -/
theorem Circuit.maxDepth_cons (c : Circuit n) (cs : List (Circuit n)) :
    Circuit.maxDepth (c :: cs) = max c.depth (Circuit.maxDepth cs) := rfl

/-- `sumSize` of the empty list. -/
theorem Circuit.sumSize_nil : Circuit.sumSize ([] : List (Circuit n)) = 0 := rfl

/-- `sumSize` on a cons cell. -/
theorem Circuit.sumSize_cons (c : Circuit n) (cs : List (Circuit n)) :
    Circuit.sumSize (c :: cs) = c.size + Circuit.sumSize cs := rfl

/-- `Circuit.maxFaninL` of the empty list. -/
theorem Circuit.maxFaninL_nil : Circuit.maxFaninL ([] : List (Circuit n)) = 0 := rfl

/-- `Circuit.maxFaninL` on a cons cell. -/
theorem Circuit.maxFaninL_cons (c : Circuit n) (cs : List (Circuit n)) :
    Circuit.maxFaninL (c :: cs) = max c.maxFanin (Circuit.maxFaninL cs) := rfl

/-- Each child is no deeper than the deepest. -/
theorem Circuit.depth_le_maxDepth {c : Circuit n} :
    ∀ {cs : List (Circuit n)}, c ∈ cs → c.depth ≤ Circuit.maxDepth cs
  | _ :: cs, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact (Circuit.depth_le_maxDepth h).trans (le_max_right _ _)

/-- Each child's fan-in is at most the list's. -/
theorem Circuit.maxFanin_le_maxFaninL {c : Circuit n} :
    ∀ {cs : List (Circuit n)}, c ∈ cs → c.maxFanin ≤ Circuit.maxFaninL cs
  | _ :: cs, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact (Circuit.maxFanin_le_maxFaninL h).trans (le_max_right _ _)

/-- A circuit has at least one node, so a child list is no longer than its total size. -/
theorem Circuit.length_le_sumSize : ∀ cs : List (Circuit n), cs.length ≤ Circuit.sumSize cs
  | [] => le_refl 0
  | c :: cs => by
      have hc := Circuit.one_le_size c
      have := Circuit.length_le_sumSize cs
      simp only [List.length_cons, Circuit.sumSize_cons]
      omega

/-- The list form of `Circuit.maxFanin_le_size`. -/
theorem Circuit.maxFaninL_le_sumSize :
    ∀ {cs : List (Circuit n)}, (∀ c ∈ cs, c.maxFanin ≤ c.size) →
      Circuit.maxFaninL cs ≤ Circuit.sumSize cs
  | [], _ => le_refl 0
  | c :: cs, h => by
      have h1 := h c (List.mem_cons_self ..)
      have h2 := Circuit.maxFaninL_le_sumSize (fun d hd => h d (List.mem_cons_of_mem _ hd))
      simp only [Circuit.maxFaninL_cons, Circuit.sumSize_cons]
      omega

/-- A circuit's fan-in is bounded by its size. -/
theorem Circuit.maxFanin_le_size (c : Circuit n) : c.maxFanin ≤ c.size := by
  induction c using Circuit.ind with
  | hlit l => simp [Circuit.maxFanin, Circuit.size]
  | hnode b cs ih =>
      have h₁ := Circuit.length_le_sumSize cs
      have h₂ := Circuit.maxFaninL_le_sumSize ih
      rw [Circuit.maxFanin_node, Circuit.size_node]
      omega

/-- A uniform bound on the children bounds the total size plus length. -/
private theorem Circuit.sumSize_add_length_le (m : ℕ) :
    ∀ cs : List (Circuit n), (∀ c ∈ cs, c.size + 1 ≤ m) →
      Circuit.sumSize cs + cs.length ≤ cs.length * m
  | [], _ => by simp [Circuit.sumSize_nil]
  | c :: cs, h => by
      have ih := Circuit.sumSize_add_length_le m cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hc := h c (List.mem_cons_self ..)
      simp only [Circuit.sumSize_cons, List.length_cons, Nat.succ_mul]
      omega

/-- A fan-in-2 circuit of depth `d` has at most `2 ^ (d + 1) - 1` nodes. -/
theorem Circuit.size_succ_le_two_pow : ∀ c : Circuit n, c.maxFanin ≤ 2 →
    c.size + 1 ≤ 2 ^ (c.depth + 1) := by
  intro c
  induction c using Circuit.ind with
  | hlit l => intro _; simp [Circuit.size, Circuit.depth]
  | hnode b cs ih =>
      intro h
      rw [Circuit.maxFanin_node] at h
      have hlen : cs.length ≤ 2 := le_trans (le_max_left _ _) h
      have hfan : Circuit.maxFaninL cs ≤ 2 := le_trans (le_max_right _ _) h
      have hchild : ∀ c ∈ cs, c.size + 1 ≤ 2 ^ (Circuit.maxDepth cs + 1) := fun c hc =>
        le_trans (ih c hc (le_trans (Circuit.maxFanin_le_maxFaninL hc) hfan))
          (Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_succ (Circuit.depth_le_maxDepth hc)))
      have hsum := Circuit.sumSize_add_length_le _ cs hchild
      have hpos : 1 ≤ 2 ^ (Circuit.maxDepth cs + 1) := Nat.one_le_two_pow
      have hD : (2 : ℕ) ^ (Circuit.maxDepth cs + 2) = 2 * 2 ^ (Circuit.maxDepth cs + 1) := by
        ring
      rw [Circuit.size_node, Circuit.depth_node, show (1 : ℕ) + Circuit.maxDepth cs + 1
        = Circuit.maxDepth cs + 2 from by omega]
      rcases Nat.lt_or_ge cs.length 1 with hz | hz
      · have hnil : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hnil
        simp only [Circuit.sumSize_nil]
        omega
      · rcases Nat.lt_or_ge cs.length 2 with hz2 | hz2
        · rw [show cs.length = 1 from by omega, Nat.one_mul] at hsum
          omega
        · rw [show cs.length = 2 from by omega] at hsum
          omega

-- ----------------------------------------------------------------
-- Section 3: Normal-form circuit (alternating, nodup at base)
-- ----------------------------------------------------------------

/-! The alternating normal form — alternating trees over base clauses (see the
module docstring's Divergences; **not** [OD14, Def 4.26]'s layered circuits) —
with [OD14, Def 4.27]'s condition that a base gate reads no variable twice as
the `Nodup` invariant. -/

mutual
/-- A normal-form circuit whose root is an `AND`: either a base `clause` of
    literals with pairwise distinct variable indices, or a `node` over
    `OR`-rooted children. -/
inductive NAndCircuit (n : Nat) where
  | clause : (lits : List (Lit n)) → (lits.map Lit.idx).Nodup → NAndCircuit n
  | node   : List (NOrCircuit n) → NAndCircuit n

/-- A normal-form circuit whose root is an `OR`: either a base `clause` of
    literals with pairwise distinct variable indices, or a `node` over
    `AND`-rooted children. -/
inductive NOrCircuit (n : Nat) where
  | clause : (lits : List (Lit n)) → (lits.map Lit.idx).Nodup → NOrCircuit n
  | node   : List (NAndCircuit n) → NOrCircuit n
end

-- Evaluation
mutual
/-- Evaluate an `AND`-rooted normal-form circuit: a clause is the conjunction of
    its literals, a node the conjunction of its children. -/
def NAndCircuit.eval : NAndCircuit n → (Fin n → Bool) → Bool
  | .clause lits _, x => lits.foldr (fun l acc => l.eval x && acc) true
  | .node cs, x       => cs.foldr (fun c acc => c.eval x && acc) true

/-- Evaluate an `OR`-rooted normal-form circuit: a clause is the disjunction of
    its literals, a node the disjunction of its children. -/
def NOrCircuit.eval : NOrCircuit n → (Fin n → Bool) → Bool
  | .clause lits _, x => lits.foldr (fun l acc => l.eval x || acc) false
  | .node cs, x       => cs.foldr (fun c acc => c.eval x || acc) false
end

-- Literal count
mutual
/-- Literal occurrences in an `AND`-rooted normal-form circuit: a clause's length,
    a node's the sum over its children. -/
def NAndCircuit.litCount : NAndCircuit n → Nat
  | .clause lits _ => lits.length
  | .node cs       => cs.foldr (fun c acc => c.litCount + acc) 0

/-- Literal occurrences in an `OR`-rooted normal-form circuit: a clause's length,
    a node's the sum over its children. -/
def NOrCircuit.litCount : NOrCircuit n → Nat
  | .clause lits _ => lits.length
  | .node cs       => cs.foldr (fun c acc => c.litCount + acc) 0
end

-- Total node count (size)
mutual
/-- Node count of an `AND`-rooted normal-form circuit: a clause is one node, a
    node one plus the sum over its children. -/
def NAndCircuit.size : NAndCircuit n → Nat
  | .clause _ _ => 1
  | .node cs    => 1 + cs.foldr (fun c acc => c.size + acc) 0

/-- Node count of an `OR`-rooted normal-form circuit: a clause is one node, a
    node one plus the sum over its children. -/
def NOrCircuit.size : NOrCircuit n → Nat
  | .clause _ _ => 1
  | .node cs    => 1 + cs.foldr (fun c acc => c.size + acc) 0
end

-- Depth
mutual
/-- Depth of an `AND`-rooted normal-form circuit: a clause has depth `0`, a node
    one more than its deepest child. -/
def NAndCircuit.depth : NAndCircuit n → Nat
  | .clause _ _ => 0
  | .node cs    => 1 + cs.foldr (fun c acc => max c.depth acc) 0

/-- Depth of an `OR`-rooted normal-form circuit: a clause has depth `0`, a node
    one more than its deepest child. -/
def NOrCircuit.depth : NOrCircuit n → Nat
  | .clause _ _ => 0
  | .node cs    => 1 + cs.foldr (fun c acc => max c.depth acc) 0
end

-- ----------------------------------------------------------------
-- Section 4: Properties that hold by construction (hnodup / hnd)
-- ----------------------------------------------------------------

/-- The `Nodup` invariant of an `AND`-rooted base clause, read back off the
    constructor. -/
theorem NAndCircuit.clause_nodup {n : Nat} {c : NAndCircuit n} {lits : List (Lit n)}
    {h : (lits.map Lit.idx).Nodup}
    (_ : c = NAndCircuit.clause lits h) : (lits.map Lit.idx).Nodup := h

/-- The `Nodup` invariant of an `OR`-rooted base clause, read back off the
    constructor. -/
theorem NOrCircuit.clause_nodup {n : Nat} {c : NOrCircuit n} {lits : List (Lit n)}
    {h : (lits.map Lit.idx).Nodup}
    (_ : c = NOrCircuit.clause lits h) : (lits.map Lit.idx).Nodup := h

/-- In every clause of a normal-form circuit, if two literals share the same
    variable index then they are identical. -/
theorem Lit.eq_of_idx_eq_of_mem_nodup
    {lits : List (Lit n)} (hnd : (lits.map Lit.idx).Nodup)
    {l₁ l₂ : Lit n} (h₁ : l₁ ∈ lits) (h₂ : l₂ ∈ lits) (hidx : l₁.idx = l₂.idx) :
    l₁ = l₂ := by
      have := List.nodup_iff_injective_get.mp hnd
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp h₁
      obtain ⟨ j, hj ⟩ := List.mem_iff_get.mp h₂
      simp_all +decide
      have := @this ⟨ i, by simp ⟩ ⟨ j, by simp ⟩
      aesop

-- ----------------------------------------------------------------
-- Section 5: Normalization : Circuit → Normal-form circuit
-- ----------------------------------------------------------------

mutual
/-- Normalize into `AND`-rooted alternating form: a leaf becomes a one-literal
    clause, an `AND` gate maps its children into `OR` form, and an `OR` gate
    becomes a one-child `AND` node over an `OR` node. -/
def Circuit.toNAnd : Circuit n → NAndCircuit n
  | .lit l          => .clause [l] (List.nodup_singleton _)
  | .node true  cs  => .node (cs.map Circuit.toNOr)
  | .node false cs  => .node [NOrCircuit.node (cs.map Circuit.toNAnd)]

/-- Normalize into `OR`-rooted alternating form: a leaf becomes a one-literal
    clause, an `OR` gate maps its children into `AND` form, and an `AND` gate
    becomes a one-child `OR` node over an `AND` node. -/
def Circuit.toNOr : Circuit n → NOrCircuit n
  | .lit l          => .clause [l] (List.nodup_singleton _)
  | .node false cs  => .node (cs.map Circuit.toNAnd)
  | .node true  cs  => .node [NAndCircuit.node (cs.map Circuit.toNOr)]
end

/-- Folding `&&` after `List.map h` agrees with folding `&&` directly, when
    `g (h c) = f c` on every element. -/
private theorem foldr_and_map {α β : Type*} {f : α → Bool} {g : β → Bool} {h : α → β}
    {cs : List α}
    (heq : ∀ c ∈ cs, g (h c) = f c) :
    (cs.map h).foldr (fun c acc => g c && acc) true =
    cs.foldr (fun c acc => f c && acc) true := by
      induction cs <;> aesop

/-- Folding `||` after `List.map h` agrees with folding `||` directly, when
    `g (h c) = f c` on every element. -/
private theorem foldr_or_map {α β : Type*} {f : α → Bool} {g : β → Bool} {h : α → β}
    {cs : List α}
    (heq : ∀ c ∈ cs, g (h c) = f c) :
    (cs.map h).foldr (fun c acc => g c || acc) false =
    cs.foldr (fun c acc => f c || acc) false := by
      induction cs <;> aesop

/-- Summing after `List.map h` agrees with summing directly, when
    `g (h c) = f c` on every element. -/
private theorem foldr_add_map {α β : Type*} {f : α → Nat} {g : β → Nat} {h : α → β}
    {cs : List α}
    (heq : ∀ c ∈ cs, g (h c) = f c) :
    (cs.map h).foldr (fun c acc => g c + acc) 0 =
    cs.foldr (fun c acc => f c + acc) 0 := by
      induction cs <;> aesop

/-- If `g (h c) ≤ k * f c` on every element, the sum after `List.map h` is at
    most `k` times the direct sum. -/
private theorem foldr_add_map_le {α β : Type*} {f : α → Nat} {g : β → Nat} {h : α → β}
    {cs : List α} {k : Nat}
    (heq : ∀ c ∈ cs, g (h c) ≤ k * f c) :
    (cs.map h).foldr (fun c acc => g c + acc) 0 ≤
    k * cs.foldr (fun c acc => f c + acc) 0 := by
      induction' cs with c cs ih
      · simp +decide
      · simp +zetaDelta at *
        linarith [ ih heq.2 ]

/-- Combined semantics preservation theorem (proves both toNAnd and toNOr at once). -/
theorem toNAnd_toNOr_eval (c : Circuit n) (x : Fin n → Bool) :
    (c.toNAnd).eval x = c.eval x ∧ (c.toNOr).eval x = c.eval x := by
      induction' c using Circuit.ind with l isAnd cs ih
      · repeat' unfold Circuit.toNAnd Circuit.toNOr
        unfold NAndCircuit.eval NOrCircuit.eval Circuit.eval; aesop
      · unfold Circuit.toNAnd Circuit.toNOr Circuit.eval
        cases isAnd <;> simp +decide [ * ]
        · simp [NAndCircuit.eval]
          unfold NOrCircuit.eval; simp +decide [ List.foldr_map ]
          induction cs <;> aesop
        · unfold NOrCircuit.eval; simp +decide
          unfold NAndCircuit.eval
          induction cs <;> aesop

/-- `toNAnd` preserves semantics. -/
theorem toNAnd_eval (c : Circuit n) (x : Fin n → Bool) :
    (c.toNAnd).eval x = c.eval x := (toNAnd_toNOr_eval c x).1

/-- `toNOr` preserves semantics. -/
theorem toNOr_eval (c : Circuit n) (x : Fin n → Bool) :
    (c.toNOr).eval x = c.eval x := (toNAnd_toNOr_eval c x).2

/-- Combined literal-count preservation.

**Proof sketch.** The two halves are proved together, by structural induction on
the circuit, because normalizing an AND gate calls the OR normalization on the
children and vice versa.  A leaf becomes a one-literal clause, so both counts are
`1`.  At a gate, one normalization maps the children directly and the other wraps
them in a single extra node; an extra node holds no literals, so in both cases
the count is the sum over the children of their normalized counts.  A side
induction on the child list then turns the induction hypothesis for each child
into equality of the two folded sums. -/
theorem toNAnd_toNOr_litCount (c : Circuit n) :
    (c.toNAnd).litCount = c.litCount ∧ (c.toNOr).litCount = c.litCount := by
      by_contra h_contra
      revert h_contra
      induction' c using Circuit.ind with l isAnd cs ih
      · unfold Circuit.toNAnd Circuit.toNOr
        unfold NAndCircuit.litCount NOrCircuit.litCount Circuit.litCount; aesop
      · cases isAnd <;> simp_all +decide
        · unfold Circuit.toNAnd Circuit.toNOr
          unfold NAndCircuit.litCount NOrCircuit.litCount Circuit.litCount
          induction cs <;> simp_all +decide [ List.foldr ]
        · unfold Circuit.toNAnd Circuit.toNOr
          constructor
          · unfold NAndCircuit.litCount Circuit.litCount
            have h_foldr : ∀ (cs : List (Circuit n)),
                (∀ c ∈ cs, c.toNOr.litCount = c.litCount) →
                List.foldr (fun c acc => c.litCount + acc) 0 (List.map Circuit.toNOr cs) =
                List.foldr (fun c acc => c.litCount + acc) 0 cs := by
              intros cs hcs; induction cs <;> aesop
            exact h_foldr cs fun c hc => ih c hc |>.2
          · unfold NOrCircuit.litCount Circuit.litCount; simp +decide
            unfold NAndCircuit.litCount
            have h_foldr : ∀ (cs : List (Circuit n)),
                (∀ c ∈ cs, c.toNOr.litCount = c.litCount) →
                List.foldr (fun c acc => c.litCount + acc) 0 (List.map Circuit.toNOr cs) =
                List.foldr (fun c acc => c.litCount + acc) 0 cs := by
              intros cs hcs; induction cs <;> aesop
            exact h_foldr cs fun c hc => ih c hc |>.2

/-- `toNAnd` preserves the literal count. -/
theorem toNAnd_litCount (c : Circuit n) :
    (c.toNAnd).litCount = c.litCount := (toNAnd_toNOr_litCount c).1

/-- `toNOr` preserves the literal count. -/
theorem toNOr_litCount (c : Circuit n) :
    (c.toNOr).litCount = c.litCount := (toNAnd_toNOr_litCount c).2

/-- Combined size bound.

**Proof sketch.** Structural induction, again proving the two halves together.  A
leaf normalizes to a single clause: size one against a circuit of size one.  At a
gate, the normalization whose connective matches the gate maps the children
directly, giving size one plus the sum of the children's normalized sizes, while
the other inserts one node to restore alternation, giving two plus that sum.  The
step doing the work in each case is the list bound: if every child's normalized
size is at most twice its own, the sum of the normalized sizes is at most twice
the sum of the sizes.  The gate's own size is one more than the children's total,
so twice the gate's size leaves two units of slack over twice the children's
total — exactly enough to pay for the inserted node. -/
theorem toNAnd_toNOr_size_le (c : Circuit n) :
    (c.toNAnd).size ≤ 2 * c.size ∧ (c.toNOr).size ≤ 2 * c.size := by
      induction' c using Circuit.ind with l isAnd cs ih
      · simp +arith +decide [ Circuit.toNAnd, Circuit.toNOr ]
        exact ⟨ by simp +arith +decide [ NAndCircuit.size, Circuit.size ],
                by simp +arith +decide [ NOrCircuit.size, Circuit.size ] ⟩
      · have h_ind : ∀ c ∈ cs, c.toNAnd.size ≤ 2 * c.size ∧ c.toNOr.size ≤ 2 * c.size :=
          ih
        unfold Circuit.toNAnd Circuit.toNOr Circuit.size
        cases isAnd <;> simp +decide [ * ]
        · constructor
          · simp +arith +decide [ NAndCircuit.size ]
            unfold NOrCircuit.size; simp +arith +decide [ * ]
            have h_foldr : ∀ (cs : List (Circuit n)),
                (∀ c ∈ cs, c.toNAnd.size ≤ 2 * c.size) →
                List.foldr (fun c acc => acc + c.size) 0 (List.map Circuit.toNAnd cs) ≤
                2 * List.foldr (fun c acc => acc + c.size) 0 cs := by
              intro cs h_ind; induction cs <;> simp_all +decide [ mul_add ]
              grind
            exact h_foldr cs fun c hc => h_ind c hc |>.1
          · unfold NOrCircuit.size
            have h_foldr :
                List.foldr (fun c acc => c.size + acc) 0 (List.map Circuit.toNAnd cs) ≤
                2 * List.foldr (fun c acc => c.size + acc) 0 cs := by
              convert foldr_add_map_le _ using 1
              exact fun c hc => h_ind c hc |>.1
            linarith
        · have h_node :
              (List.foldr (fun c acc => c.toNOr.size + acc) 0 cs) ≤
              2 * (List.foldr (fun c acc => c.size + acc) 0 cs) := by
            have h_node : ∀ (cs : List (Circuit n)),
                (∀ c ∈ cs, c.toNOr.size ≤ 2 * c.size) →
                (List.foldr (fun c acc => c.toNOr.size + acc) 0 cs) ≤
                2 * (List.foldr (fun c acc => c.size + acc) 0 cs) := by
              intros cs hcs; induction cs <;> simp_all +decide [ mul_add ]
              linarith
            exact h_node cs fun c hc => h_ind c hc |>.2
          constructor
          · unfold NAndCircuit.size; simp +arith +decide [ * ]
            convert Nat.le_succ_of_le h_node using 1
            · clear h_ind h_node ih
              induction cs <;> simp +decide [ * ]
              ring
            · simp +arith +decide [ add_comm ]
          · simp +arith +decide [ NOrCircuit.size ]
            simp +arith +decide [ NAndCircuit.size ]
            convert h_node using 1
            · clear h_ind h_node ih
              induction cs <;> simp +decide [ * ]
              ring
            · ac_rfl

/-- `toNAnd` at most doubles the size. -/
theorem toNAnd_size_le (c : Circuit n) :
    (c.toNAnd).size ≤ 2 * c.size := (toNAnd_toNOr_size_le c).1

/-- `toNOr` at most doubles the size. -/
theorem toNOr_size_le (c : Circuit n) :
    (c.toNOr).size ≤ 2 * c.size := (toNAnd_toNOr_size_le c).2

-- ----------------------------------------------------------------
-- Section 6: Coercion: NCircuit → Circuit (forgetful map)
-- ----------------------------------------------------------------

mutual
/-- Forget the normal form: a clause becomes an `AND` gate over its literal
    leaves, a node an `AND` gate over its converted children. -/
def NAndCircuit.toCircuit : NAndCircuit n → Circuit n
  | .clause lits _ => .node true (lits.map fun l => .lit l)
  | .node cs       => .node true (cs.map NOrCircuit.toCircuit)

/-- Forget the normal form: a clause becomes an `OR` gate over its literal
    leaves, a node an `OR` gate over its converted children. -/
def NOrCircuit.toCircuit : NOrCircuit n → Circuit n
  | .clause lits _ => .node false (lits.map fun l => .lit l)
  | .node cs       => .node false (cs.map NAndCircuit.toCircuit)
end

-- ----------------------------------------------------------------
-- Section 7: Useful derived API
-- ----------------------------------------------------------------

/-- Build a single-variable AND-circuit. -/
def NAndCircuit.ofVar (i : Fin n) : NAndCircuit n :=
  .clause [⟨i, true⟩] (List.nodup_singleton _)

/-- Build a single-variable OR-circuit. -/
def NOrCircuit.ofVar (i : Fin n) : NOrCircuit n :=
  .clause [⟨i, true⟩] (List.nodup_singleton _)

/-- The constant-true AND-circuit (empty conjunction). -/
def NAndCircuit.constTrue : NAndCircuit n :=
  .clause [] List.nodup_nil

/-- The constant-false OR-circuit (empty disjunction). -/
def NOrCircuit.constFalse : NOrCircuit n :=
  .clause [] List.nodup_nil

end BoolCircuit

## ===== TCSlib/Complexity/CircuitComplexity/CircuitSat.lean =====

/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.Complexity.CircuitComplexity.Basic
import TCSlib.Complexity.NPReductions.SATTo3SAT

/-!
# CKT-SAT, and the Tseitin reduction to 3SAT

Arora–Barak Definition 6.9 and Lemma 6.11.

## Main definitions

* `BoolCircuit.Circuit.Satisfiable`, `BoolCircuit.CktSat` — [AB09, Def 6.9].
* `BoolCircuit.CktVar` — the Tseitin variables: one per input, one per subcircuit.
* `BoolCircuit.Circuit.toCNF` — the gate clauses plus the output unit clause.

## Main results

* `BoolCircuit.Circuit.satisfiable_iff_isSatisfiable` — both directions of
  [AB09, Lem 6.11], before the 3-CNF step.
* `BoolCircuit.mem_cktSat_iff_is3Satisfiable` — [AB09, Lem 6.11], equisatisfiability only.
* `BoolCircuit.Circuit.toCNF_length_le` — the intermediate `C.toCNF` has at most
  `3 * C.size` clauses.

## Divergences from Arora–Barak §6.1.2

Only equisatisfiability is formalized, not `≤p`: this file proves no bound on the
reduction's *cost*.  The campaign's machine model and class `P` live on this branch
(`TuringMachine/`, `ClassP/`); what is missing here is a machine-level implementation
of the reduction. `toCNF_length_le` counts the clauses of the
intermediate `C.toCNF` and no more — clause *width* is unbounded (see fan-in below),
and `CktVar n`, indexed by all of `Circuit n`, is infinite, so the output formula has no
bit length here.  Relatedly, AB's CKT-SAT is a language of *strings representing*
circuits, whereas `CktSat` is a set of circuits: the Tseitin proof must not depend on an
encoding.  `CircuitComplexity.Encoding` supplies one downstream, and with it a clause
count bounded in the encoded input length — still not a `≤p` claim.

Model: `BoolCircuit.Circuit`, a tree, not the DAG `BoolCircuit.FeedForward` of `PPoly.lean`. The
tree is the chosen carrier, not a forced one: a gate's
membership in these gate sets *can* be cased on: `RazborovSmolensky.ACp_GateOps_cases`
(`ACpGates.lean:579`) does it for `ACp_GateOps p`, unfolding the `⋃` through
`Set.mem_iUnion.mp`, and `ACp_GateOps = stdGateOps ∪ ⋃ n, {modGateOp p n}` — no
`stdGateOps_cases` exists, but nothing obstructs one.  A clause map over `FeedForward` is
**unimplemented, not impossible**: `id` and `NOT` each admit two binary Tseitin
clauses (they lack `Circuit` *nodes*, which only blocks reuse of this file's
unroller), and the dependent sum of layer/node types — the same index
`FeedForward.size` counts — would serve as a Tseitin variable type.  Missing
are that implementation and its cost bounds.  No equivalence of the two models is claimed, and none is
available here. `Circuit` has no `NOT` gate — negation
lives in the leaf literals — so AB's `zᵢ ↔ ¬z_j` pair occurs exactly at a negative leaf.

Fan-in stays unbounded, as in `PPoly.lean`, so a width-`w` `AND` needs one clause of
width `w + 1` and `toCNF` is CNF, not 3-CNF; rather than pre-reduce to fan-in 2 we
compose with `SATTo3SAT.to3SAT`. Equal subcircuits share a variable — Tseitin sharing.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

open SATTo3SAT

variable {n : ℕ}

/-! ## CKT-SAT -/

/-- A circuit is satisfiable when some input makes it output `true`. -/
def Circuit.Satisfiable (C : Circuit n) : Prop :=
  ∃ u : Fin n → Bool, C.eval u = true

/-- CKT-SAT: the satisfiable circuits, indexed by their arity.  [AB09, Def 6.9] -/
def CktSat : Set ((n : ℕ) × Circuit n) :=
  {C | C.2.Satisfiable}

/-- Membership in `CktSat` is satisfiability of the underlying circuit. -/
@[simp]
theorem mem_cktSat_iff (C : (n : ℕ) × Circuit n) : C ∈ CktSat ↔ C.2.Satisfiable :=
  Iff.rfl

/-! `CktSat` is neither empty nor everything: on zero inputs the empty `AND` is
satisfiable and the empty `OR` is not. -/

example : (⟨0, .node true []⟩ : (n : ℕ) × Circuit n) ∈ CktSat :=
  ⟨finZeroElim, by simp [Circuit.eval]⟩

example : (⟨0, .node false []⟩ : (n : ℕ) × Circuit n) ∉ CktSat := by
  rintro ⟨u, hu⟩
  simp [Circuit.eval] at hu

/-! ## The Tseitin encoding -/

/-- The variables of the encoding: the circuit's inputs, and one per subcircuit. -/
inductive CktVar (n : ℕ) where
  | input : Fin n → CktVar n
  | gate : Circuit n → CktVar n

/-- The literal over `CktVar n` that holds exactly when the leaf literal `l` does. -/
def Lit.toCktLiteral (l : Lit n) : Literal (CktVar n) :=
  if l.sign then .pos (.input l.idx) else .neg (.input l.idx)

/-- The negation of `Lit.toCktLiteral l`. -/
def Lit.toCktLiteralNeg (l : Lit n) : Literal (CktVar n) :=
  if l.sign then .neg (.input l.idx) else .pos (.input l.idx)

/-- The clauses forcing `z ↔ ⋀ zᵢ` (`isAnd = true`) or `z ↔ ⋁ zᵢ`, where `z` is the
variable of `node isAnd cs` and the `zᵢ` are those of its children. -/
def gateClauses : Bool → List (Circuit n) → CNFFormula (CktVar n)
  | true, cs =>
      (Literal.pos (.gate (.node true cs)) :: cs.map fun c => Literal.neg (.gate c)) ::
        cs.map fun c => [Literal.neg (.gate (.node true cs)), Literal.pos (.gate c)]
  | false, cs =>
      (Literal.neg (.gate (.node false cs)) :: cs.map fun c => Literal.pos (.gate c)) ::
        cs.map fun c => [Literal.pos (.gate (.node false cs)), Literal.neg (.gate c)]

/-- The gate clauses of every subcircuit of `C`. -/
def Circuit.tseitin : Circuit n → CNFFormula (CktVar n)
  | .lit l =>
      [[Literal.neg (.gate (.lit l)), l.toCktLiteral],
       [Literal.pos (.gate (.lit l)), l.toCktLiteralNeg]]
  | .node b cs => gateClauses b cs ++ cs.flatMap fun c => c.tseitin

/-- The CNF formula the reduction produces: the gate clauses together with the unit
clause on the output node. -/
def Circuit.toCNF (C : Circuit n) : CNFFormula (CktVar n) :=
  [Literal.pos (.gate C)] :: C.tseitin

/-- The assignment reading the inputs off `u` and every subcircuit variable off that
subcircuit's value. -/
def tseitinAssignment (u : Fin n → Bool) : CktVar n → Prop
  | .input i => u i = true
  | .gate D => D.eval u = true

/-! ## Correctness -/

/-- A leaf literal's translation holds exactly when the leaf literal does. -/
theorem evalLiteral_toCktLiteral_iff {α : Assignment (CktVar n)} {u : Fin n → Bool}
    (hu : ∀ i, u i = true ↔ α (CktVar.input i)) (l : Lit n) :
    evalLiteral α l.toCktLiteral ↔ l.eval u = true := by
  cases hs : l.sign <;> cases hb : u l.idx <;>
    simp [Lit.toCktLiteral, evalLiteral, hs, hb, ← hu l.idx]

/-- `Lit.toCktLiteralNeg` translates the negation of a leaf literal. -/
theorem evalLiteral_toCktLiteralNeg_iff {α : Assignment (CktVar n)} {u : Fin n → Bool}
    (hu : ∀ i, u i = true ↔ α (CktVar.input i)) (l : Lit n) :
    evalLiteral α l.toCktLiteralNeg ↔ ¬ (l.eval u = true) := by
  cases hs : l.sign <;> cases hb : u l.idx <;>
    simp [Lit.toCktLiteralNeg, evalLiteral, hs, hb, ← hu l.idx]

/-- The canonical assignment satisfies the clauses of any one gate.

**Proof sketch.** Split on the gate's connective; the two cases are dual, with
every polarity exchanged.  Take the OR gate.  Its clause set is one long clause
saying that if the gate's variable holds then some child's does, together with
one short clause per child saying the converse for that child.  For the long
clause, ask whether the gate evaluates to true under the given input: if it
does, the unbounded OR semantics hand back a child that evaluates to true and
that child's positive literal is satisfied; if it does not, the gate's own
negative literal is.  For the short clause of a child, ask whether that child
evaluates to true: if it does, so does the gate, satisfying the gate's positive
literal; if it does not, the child's negative literal is satisfied.  In the AND
case the witness for the long clause in the false branch is a child that fails,
obtained by contraposing the unbounded AND semantics. -/
theorem gateClauses_satisfied (u : Fin n → Bool) (b : Bool) (cs : List (Circuit n)) :
    formulaSatisfied (tseitinAssignment u) (gateClauses b cs) := by
  cases b
  · intro c hc
    simp only [gateClauses, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨d, hd, rfl⟩
    · by_cases hz : (Circuit.node false cs).eval u = true
      · obtain ⟨d, hd, hdv⟩ := (Circuit.eval_node_false_iff cs u).mp hz
        exact ⟨Literal.pos (.gate d),
          List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d, hd, rfl⟩), hdv⟩
      · exact ⟨Literal.neg (.gate (.node false cs)), List.mem_cons_self, hz⟩
    · by_cases hdv : d.eval u = true
      · exact ⟨Literal.pos (.gate (.node false cs)), List.mem_cons_self,
          (Circuit.eval_node_false_iff cs u).mpr ⟨d, hd, hdv⟩⟩
      · exact ⟨Literal.neg (.gate d), List.mem_cons_of_mem _ List.mem_cons_self, hdv⟩
  · intro c hc
    simp only [gateClauses, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨d, hd, rfl⟩
    · by_cases hz : (Circuit.node true cs).eval u = true
      · exact ⟨Literal.pos (.gate (.node true cs)), List.mem_cons_self, hz⟩
      · obtain ⟨d, hd, hdv⟩ : ∃ d ∈ cs, ¬ d.eval u = true := by
          by_contra hcon
          push_neg at hcon
          exact hz ((Circuit.eval_node_true_iff cs u).mpr hcon)
        exact ⟨Literal.neg (.gate d),
          List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d, hd, rfl⟩), hdv⟩
    · by_cases hz : (Circuit.node true cs).eval u = true
      · exact ⟨Literal.pos (.gate d), List.mem_cons_of_mem _ List.mem_cons_self,
          (Circuit.eval_node_true_iff cs u).mp hz d hd⟩
      · exact ⟨Literal.neg (.gate (.node true cs)), List.mem_cons_self, hz⟩

/-- The canonical assignment satisfies every gate clause of `C`.

**Proof sketch.** Structural induction on the circuit.  At a leaf the encoding
contributes the two clauses expressing that the leaf's variable is equivalent to
the leaf literal; the canonical assignment gives that variable exactly the
leaf's value, so splitting on that value picks, in each of the two clauses, a
literal that holds.  At a gate the clause set is the gate's own clauses followed
by the clauses of the children: the first are covered by the preceding lemma,
the second by the induction hypothesis. -/
theorem tseitin_satisfied (u : Fin n → Bool) (C : Circuit n) :
    formulaSatisfied (tseitinAssignment u) C.tseitin := by
  have hu : ∀ i, u i = true ↔ tseitinAssignment u (CktVar.input i) := fun _ => Iff.rfl
  induction C using Circuit.ind with
  | hlit l =>
      intro c hc
      have e1 := evalLiteral_toCktLiteral_iff (α := tseitinAssignment u) hu l
      have e2 := evalLiteral_toCktLiteralNeg_iff (α := tseitinAssignment u) hu l
      have hval : tseitinAssignment u (CktVar.gate (.lit l)) ↔ l.eval u = true := by
        simp [tseitinAssignment, Circuit.eval_lit]
      simp only [Circuit.tseitin, List.mem_cons, List.not_mem_nil, or_false] at hc
      by_cases hg : l.eval u = true
      · rcases hc with rfl | rfl
        · exact ⟨l.toCktLiteral, List.mem_cons_of_mem _ List.mem_cons_self, e1.mpr hg⟩
        · exact ⟨Literal.pos (.gate (.lit l)), List.mem_cons_self, hval.mpr hg⟩
      · rcases hc with rfl | rfl
        · exact ⟨Literal.neg (.gate (.lit l)), List.mem_cons_self, fun hh => hg (hval.mp hh)⟩
        · exact ⟨l.toCktLiteralNeg, List.mem_cons_of_mem _ List.mem_cons_self, e2.mpr hg⟩
  | hnode b cs ih =>
      intro c hc
      simp only [Circuit.tseitin, List.mem_append, List.mem_flatMap] at hc
      rcases hc with hc | ⟨d, hd, hcd⟩
      · exact gateClauses_satisfied u b cs c hc
      · exact ih d hd c hcd

/-- The gate clauses of one gate pin its variable to the gate's value, given that the
children's variables are already correct.

**Proof sketch.** Split on the connective; again the two cases are dual.  Read
two facts off the clause set: from the long clause, that the gate's variable
implies the disjunction of the children's variables (OR case) or is implied by
their conjunction (AND case); and from the short clauses, one per child, the
converse implication for that child.  Unfold the gate's semantics — an OR gate
is true exactly when some child is, an AND gate exactly when all are — and each
direction of the goal is one of those two facts composed with the hypothesis
that every child's variable already agrees with that child's value. -/
theorem eval_node_iff_of_gateClauses {α : Assignment (CktVar n)} {u : Fin n → Bool}
    (b : Bool) (cs : List (Circuit n)) (hgate : formulaSatisfied α (gateClauses b cs))
    (key : ∀ c ∈ cs, (c.eval u = true ↔ α (CktVar.gate c))) :
    (Circuit.node b cs).eval u = true ↔ α (CktVar.gate (.node b cs)) := by
  cases b
  · have hmain : ¬ α (CktVar.gate (.node false cs)) ∨ ∃ c ∈ cs, α (CktVar.gate c) := by
      simpa [clauseSatisfied, evalLiteral] using
        hgate (Literal.neg (.gate (.node false cs)) :: cs.map fun c => Literal.pos (.gate c))
          List.mem_cons_self
    have hside : ∀ c ∈ cs, α (CktVar.gate (.node false cs)) ∨ ¬ α (CktVar.gate c) := by
      intro c hc
      simpa [clauseSatisfied, evalLiteral] using
        hgate [Literal.pos (.gate (.node false cs)), Literal.neg (.gate c)]
          (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
    rw [Circuit.eval_node_false_iff]
    constructor
    · rintro ⟨c, hc, hcv⟩
      exact (hside c hc).resolve_right (not_not_intro ((key c hc).mp hcv))
    · intro hz
      obtain ⟨c, hc, hcv⟩ := hmain.resolve_left (not_not_intro hz)
      exact ⟨c, hc, (key c hc).mpr hcv⟩
  · have hmain : α (CktVar.gate (.node true cs)) ∨ ∃ c ∈ cs, ¬ α (CktVar.gate c) := by
      simpa [clauseSatisfied, evalLiteral] using
        hgate (Literal.pos (.gate (.node true cs)) :: cs.map fun c => Literal.neg (.gate c))
          List.mem_cons_self
    have hside : ∀ c ∈ cs, ¬ α (CktVar.gate (.node true cs)) ∨ α (CktVar.gate c) := by
      intro c hc
      simpa [clauseSatisfied, evalLiteral] using
        hgate [Literal.neg (.gate (.node true cs)), Literal.pos (.gate c)]
          (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
    rw [Circuit.eval_node_true_iff]
    constructor
    · intro hall
      refine hmain.resolve_right ?_
      rintro ⟨c, hc, hnc⟩
      exact hnc ((key c hc).mp (hall c hc))
    · intro hz c hc
      exact (key c hc).mpr ((hside c hc).resolve_left (not_not_intro hz))

/-- Any assignment satisfying the gate clauses of `C` computes `C` correctly: the
soundness half of [AB09, Lem 6.11].

**Proof sketch.** Structural induction on the circuit.  At a leaf, the two
clauses expressing `z ↔ ℓ` give one implication each between the leaf's variable
and the leaf literal's value under the read-off input, and propositional
reasoning combines them into the equivalence.  At a gate, the clause set splits
into the gate's own clauses and the children's; the children's halves give, by
induction, that each child's variable agrees with its value, and the preceding
lemma then transfers that agreement to the gate itself. -/
theorem eval_iff_of_tseitin_satisfied {α : Assignment (CktVar n)} {u : Fin n → Bool}
    (hu : ∀ i, u i = true ↔ α (CktVar.input i)) (C : Circuit n)
    (h : formulaSatisfied α C.tseitin) :
    C.eval u = true ↔ α (CktVar.gate C) := by
  induction C using Circuit.ind with
  | hlit l =>
      have e1 := evalLiteral_toCktLiteral_iff hu l
      have e2 := evalLiteral_toCktLiteralNeg_iff hu l
      simp only [Circuit.tseitin] at h
      have h1 : ¬ α (CktVar.gate (.lit l)) ∨ l.eval u = true := by
        obtain ⟨p, hp, hv⟩ :=
          h [Literal.neg (.gate (.lit l)), l.toCktLiteral] List.mem_cons_self
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact Or.inl hv
        · exact Or.inr (e1.mp hv)
      have h2 : α (CktVar.gate (.lit l)) ∨ ¬ (l.eval u = true) := by
        obtain ⟨p, hp, hv⟩ := h [Literal.pos (.gate (.lit l)), l.toCktLiteralNeg]
          (List.mem_cons_of_mem _ List.mem_cons_self)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact Or.inl hv
        · exact Or.inr (e2.mp hv)
      rw [Circuit.eval_lit]
      tauto
  | hnode b cs ih =>
      refine eval_node_iff_of_gateClauses b cs (fun c hc => h c ?_) (fun c hc => ih c hc ?_)
      · simp only [Circuit.tseitin, List.mem_append]
        exact Or.inl hc
      · intro d hd
        refine h d ?_
        simp only [Circuit.tseitin, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨c, hc, hd⟩

/-- A circuit is satisfiable exactly when the CNF formula the reduction produces is.

**Proof sketch.** Each direction constructs the other side's witness.  From a
satisfying input, take the canonical assignment, which sets every gate variable
to that subcircuit's value: the output unit clause holds because the circuit
outputs true, and the gate clauses hold by the completeness lemma above.  From a
satisfying assignment, read an input off its values on the input variables: the
unit clause forces the output variable true, and the soundness lemma turns that
into the circuit evaluating to true on the read-off input. -/
theorem Circuit.satisfiable_iff_isSatisfiable (C : Circuit n) :
    C.Satisfiable ↔ isSatisfiable C.toCNF := by
  classical
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨tseitinAssignment u, ?_⟩
    intro c hc
    simp only [Circuit.toCNF, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨Literal.pos (.gate C), List.mem_cons_self, hu⟩
    · exact tseitin_satisfied u C c hc
  · rintro ⟨α, hα⟩
    refine ⟨fun i => if α (CktVar.input i) then true else false, ?_⟩
    have hu : ∀ i, (if α (CktVar.input i) then true else false) = true ↔
        α (CktVar.input i) := by
      intro i
      by_cases hi : α (CktVar.input i) <;> simp [hi]
    have hout : α (CktVar.gate C) := by
      simpa [clauseSatisfied, evalLiteral] using hα [Literal.pos (.gate C)] List.mem_cons_self
    exact (eval_iff_of_tseitin_satisfied hu C
      (fun c hc => hα c (List.mem_cons_of_mem _ hc))).mpr hout

/-- A circuit is satisfiable exactly when the 3-CNF formula built from its gate
clauses is.  [AB09, Lem 6.11] -/
theorem mem_cktSat_iff_is3Satisfiable (C : (n : ℕ) × Circuit n) :
    C ∈ CktSat ↔ is3Satisfiable (to3SAT C.2.toCNF) :=
  (C.2.satisfiable_iff_isSatisfiable).trans (SAT_to_3SAT_equivalence _)

/-! ## Size of the reduction -/

/-- The gate clauses of `C` number fewer than `3 * C.size`.

**Proof sketch.** Structural induction.  A leaf contributes two clauses against
a size of one.  At a gate the bound as stated is not strong enough to pass
through the children, because the gate also emits one short clause per child; the
induction therefore goes through a strengthened statement about lists, proved by
a side induction: the children's own clauses *together with one extra clause per
child* still fit inside three times the children's total size.  The gate's own
contribution is exactly one clause per child plus the long clause, and the
gate's size is one more than its children's total, so the three units of slack
the gate's own node contributes absorb the long clause; linear arithmetic
finishes. -/
theorem Circuit.tseitin_length_lt (C : Circuit n) :
    C.tseitin.length < 3 * C.size := by
  induction C using Circuit.ind with
  | hlit l => simp [Circuit.tseitin, Circuit.size]
  | hnode b cs ih =>
      have hlist : ∀ ds : List (Circuit n),
          (∀ d ∈ ds, d.tseitin.length < 3 * d.size) →
          (ds.flatMap fun d => d.tseitin).length + ds.length ≤
            3 * ds.foldr (fun d acc => d.size + acc) 0 := by
        intro ds hds
        induction ds with
        | nil => simp
        | cons d ds ihd =>
            have h1 := hds d List.mem_cons_self
            have h2 := ihd fun e he => hds e (List.mem_cons_of_mem _ he)
            simp only [List.flatMap_cons, List.length_append, List.length_cons,
              List.foldr_cons]
            omega
      have hsum := hlist cs ih
      have hg : (gateClauses b cs).length = cs.length + 1 := by
        cases b <;> simp [gateClauses]
      simp only [Circuit.tseitin, List.length_append, Circuit.size, hg]
      omega

/-- The reduction produces at most `3 * C.size` clauses. -/
theorem Circuit.toCNF_length_le (C : Circuit n) : C.toCNF.length ≤ 3 * C.size := by
  have h := C.tseitin_length_lt
  simp only [Circuit.toCNF, List.length_cons]
  omega

end BoolCircuit

## ===== TCSlib/Complexity/CircuitComplexity/Encoding.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Computability.Encoding
import Mathlib.Computability.Language
import TCSlib.Complexity.CircuitComplexity.CircuitSat

/-!
# Encoding circuits, CKT-SAT as a language, and the clause count of Lemma 6.11

## Main definitions

* `BoolCircuit.encodeCircuit`, `BoolCircuit.readCircuit` — a prefix serialisation of
  `BoolCircuit.Circuit` into `List Bool`, and the parser that reads it back.
* `BoolCircuit.encodeSigma`, `BoolCircuit.decodeSigma`, `BoolCircuit.circuitEncoding` — the same for an
  arity-tagged circuit, packaged as a `Computability.FinEncoding`.
* `BoolCircuit.cktSatLang` — CKT-SAT as a `Language Bool`.  [AB09, Def 6.9]

## Main results

* `BoolCircuit.decodeSigma_encodeSigma`, `BoolCircuit.encodeSigma_of_decodeSigma` — the encoding
  round-trips, and only canonical strings decode.
* `BoolCircuit.mem_cktSatLang_iff`, `BoolCircuit.mem_cktSatLang_iff_exists` — `cktSatLang` is
  exactly the image of `BoolCircuit.CktSat` under the encoding.
* `BoolCircuit.size_le_length_encodeSigma` — a circuit is never larger than its encoding
  is long, so a bound in the size is a bound in the input length.
* `BoolCircuit.length_to3SAT_toCNF_le` — the reduction of [AB09, Lem 6.11] outputs at
  most `13 * |encoding|` 3-clauses.

## Divergences from Arora–Barak §6.1.2 and §6.2

**No `≤p` claim is made or supported here.** `≤p` is polynomial-*time*
reducibility; no machine-level implementation of this reduction exists yet (the
campaign's machine model and `P` live on this branch), so its cost is bounded
nowhere and the time half of [AB09, Lem 6.11] remains unformalized, as `CircuitSat.lean` already records. What is added is a bound on
the reduction's *output*, and only on its number of 3-clauses: the output's
variable type `SATTo3SAT.AuxVar (BoolCircuit.CktVar n)` is infinite (`CktVar n`
is indexed by all of `Circuit n`), so no encoding of the output formula exists
here and its bit length is not bounded.

AB's concrete representation ([AB09, p. 112]) is the `S × S` adjacency matrix of
a size-`S` circuit's DAG plus an array of `S` gate labels, vertices identified
with `[S]`.  `BoolCircuit.Circuit` is a tree, and that representation is **not implemented**
here: a finite tree could be numbered (preorder, say) and given an adjacency
matrix, but no such numbering and none of the accessors `SIZE`/`TYPE`/`EDGE`
are defined.  AB offers the matrix as "a concrete
way", in a remark that [AB09, Def 6.14] "is robust to variations in how we
represent circuits using strings" — a robustness AB asserts rather than proves,
and which nothing below uses.  This file gives the concrete way for a tree: a
tag bit saying leaf or gate, then either the leaf's sign and variable index or
the gate's connective and its children, the children delimited by a
continue/stop bit.  Natural numbers are written in unary, which inflates the
encoding by a polynomial factor — `O(n)` rather than `O(log n)` bits for an index
below `n` — and only upwards.  Every bound below is an upper bound in the
encoding's length, so the inflation does not invalidate any of them — a longer
input only slackens a bound stated in its length — and being polynomial it
cannot break a later polynomial-time claim either (relative, always, to an
already polynomially bounded index range).

`decodeSigma` parses and then checks that the parse re-encodes to its input, so
non-canonical strings decode to `none` and are simply absent from `cktSatLang`.

`Computability.FinEncoding` is used rather than a new class: it is exactly an
encode/decode pair over a finite alphabet, and it is the interface the
Turing-machine track works against.  `Encodable`/`Denumerable` were not used
because they encode into `ℕ`, which supplies no string and so no input length
for a bound to be stated in.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

open SATTo3SAT

/-! ## Serialising a circuit -/

/-- `k` in unary: `k` `true`s terminated by a `false`. -/
private def unaryBits (k : ℕ) : List Bool := List.replicate k true ++ [false]

/-- Read one `unaryBits` block off the front of a bit string. -/
private def readUnary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (readUnary rest).map fun p => (p.1 + 1, p.2)

/-- Reading back a `unaryBits` block returns its number and the untouched remainder. -/
private theorem readUnary_unaryBits (k : ℕ) (rest : List Bool) :
    readUnary (unaryBits k ++ rest) = some (k, rest) := by
  induction k with
  | zero => simp [unaryBits, readUnary]
  | succ k ih => simpa [unaryBits, readUnary, List.replicate_succ] using ih

/-- A circuit as a bit string: a leaf is `false`, its sign, its index in unary;
a gate is `true`, its connective, then its children, each prefixed by `true` and
the list terminated by `false`. -/
def encodeCircuit {n : ℕ} : Circuit n → List Bool
  | .lit l => false :: l.sign :: unaryBits l.idx.val
  | .node b cs => (true :: b :: (cs.flatMap fun c => true :: encodeCircuit c)) ++ [false]

/-- The children block of a gate's encoding. -/
def encodeChildren {n : ℕ} (cs : List (Circuit n)) : List Bool :=
  (cs.flatMap fun c => true :: encodeCircuit c) ++ [false]

/-- A gate's encoding is its tag bit, its connective bit, then its children block. -/
theorem encodeCircuit_node {n : ℕ} (b : Bool) (cs : List (Circuit n)) :
    encodeCircuit (.node b cs) = true :: b :: encodeChildren cs := by
  simp [encodeCircuit, encodeChildren]

/-- The empty children block is the lone stop bit. -/
theorem encodeChildren_nil {n : ℕ} : encodeChildren ([] : List (Circuit n)) = [false] := by
  simp [encodeChildren]

/-- A non-empty children block is a continue bit, the head's encoding, then the
block for the tail. -/
theorem encodeChildren_cons {n : ℕ} (d : Circuit n) (ds : List (Circuit n)) :
    encodeChildren (d :: ds) = true :: (encodeCircuit d ++ encodeChildren ds) := by
  simp [encodeChildren, List.append_assoc]

/-! ## Parsing it back

Recursive descent, with a fuel argument in place of a termination measure; the
callers supply the input's length, which always suffices. -/

mutual

/-- Read one circuit off the front of a bit string, returning the remainder. -/
def readCircuit (n : ℕ) : ℕ → List Bool → Option (Circuit n × List Bool)
  | 0, _ => none
  | fuel + 1, bs =>
      match bs with
      | false :: s :: rest =>
          match readUnary rest with
          | none => none
          | some (i, r) => if h : i < n then some (.lit ⟨⟨i, h⟩, s⟩, r) else none
      | true :: b :: rest =>
          match readChildren n fuel rest with
          | none => none
          | some (cs, r) => some (.node b cs, r)
      | _ => none

/-- Read a gate's children block off the front of a bit string. -/
def readChildren (n : ℕ) : ℕ → List Bool → Option (List (Circuit n) × List Bool)
  | 0, _ => none
  | fuel + 1, bs =>
      match bs with
      | false :: rest => some ([], rest)
      | true :: rest =>
          match readCircuit n fuel rest with
          | none => none
          | some (c, r) =>
              match readChildren n fuel r with
              | none => none
              | some (cs, r') => some (c :: cs, r')
      | _ => none

end

/-- Given that each child parses back, so does a children block.

**Proof sketch.** Induction on the list of children.  The empty block is the
single stop bit, which the parser consumes outright.  A non-empty block is a
continue bit, the head child's encoding and the block for the tail, in that
order; one unit of fuel pays for the continue bit, the hypothesis for the head
returns the tail's block as its remainder, and the induction hypothesis consumes
that.  Fuel suffices at each step because the block's length is the sum of the
two sub-lengths plus one. -/
theorem readChildren_encodeChildren {n : ℕ} (ds : List (Circuit n))
    (h : ∀ d ∈ ds, ∀ (fuel : ℕ) (rest : List Bool), (encodeCircuit d).length ≤ fuel →
      readCircuit n fuel (encodeCircuit d ++ rest) = some (d, rest)) :
    ∀ (fuel : ℕ) (rest : List Bool), (encodeChildren ds).length ≤ fuel →
      readChildren n fuel (encodeChildren ds ++ rest) = some (ds, rest) := by
  induction ds with
  | nil =>
      intro fuel rest hf
      rw [encodeChildren_nil] at hf ⊢
      match fuel with
      | 0 => simp at hf
      | f + 1 => simp [readChildren]
  | cons d ds ih =>
      intro fuel rest hf
      have hd := h d List.mem_cons_self
      have ih' := ih fun e he => h e (List.mem_cons_of_mem _ he)
      rw [encodeChildren_cons] at hf ⊢
      simp only [List.length_cons, List.length_append] at hf
      match fuel with
      | 0 => simp at hf
      | f + 1 =>
          simp only [List.cons_append, readChildren, List.append_assoc]
          simp only [hd f (encodeChildren ds ++ rest) (by omega), ih' f rest (by omega)]

/-- The parser recovers any encoded circuit, given fuel at least the encoding's length.

**Proof sketch.** Structural induction on the circuit.  A leaf is a tag bit, a
sign bit and a unary index, which the unary reader returns together with the
untouched remainder; the index is in range because it came from a `Fin n`.  A
gate is a tag bit, a connective bit and a children block; the children block is
handled by the previous lemma, whose hypothesis is exactly what the induction
supplies for the children. -/
theorem readCircuit_encodeCircuit {n : ℕ} (C : Circuit n) :
    ∀ (fuel : ℕ) (rest : List Bool), (encodeCircuit C).length ≤ fuel →
      readCircuit n fuel (encodeCircuit C ++ rest) = some (C, rest) := by
  induction C using Circuit.ind with
  | hlit l =>
      intro fuel rest hf
      match fuel with
      | 0 => simp [encodeCircuit] at hf
      | f + 1 =>
          simp only [encodeCircuit, List.cons_append, readCircuit]
          rw [readUnary_unaryBits]
          simp
  | hnode b cs ih =>
      intro fuel rest hf
      rw [encodeCircuit_node] at hf ⊢
      simp only [List.length_cons] at hf
      match fuel with
      | 0 => simp at hf
      | f + 1 =>
          simp only [List.cons_append, readCircuit]
          rw [readChildren_encodeChildren cs ih f rest (by omega)]

/-! ## The encoding -/

/-- An arity-tagged circuit as a bit string: the arity in unary, then the circuit. -/
def encodeSigma : ((n : ℕ) × Circuit n) → List Bool
  | ⟨n, C⟩ => unaryBits n ++ encodeCircuit C

/-- Parse a bit string as an arity-tagged circuit, accepting only strings that
re-encode to themselves. -/
def decodeSigma (bs : List Bool) : Option ((n : ℕ) × Circuit n) :=
  match readUnary bs with
  | none => none
  | some (n, r) =>
      match readCircuit n r.length r with
      | some (C, []) => if encodeSigma ⟨n, C⟩ = bs then some ⟨n, C⟩ else none
      | _ => none

/-- Every encoded circuit decodes back to itself. -/
theorem decodeSigma_encodeSigma (C : (n : ℕ) × Circuit n) :
    decodeSigma (encodeSigma C) = some C := by
  obtain ⟨n, C⟩ := C
  simp only [decodeSigma, encodeSigma, readUnary_unaryBits]
  rw [show readCircuit n (encodeCircuit C).length (encodeCircuit C) = some (C, []) by
    simpa using readCircuit_encodeCircuit C (encodeCircuit C).length [] le_rfl]
  simp

/-- Only the encoding of `C` decodes to `C`. -/
theorem encodeSigma_of_decodeSigma {bs : List Bool} {C : (n : ℕ) × Circuit n}
    (h : decodeSigma bs = some C) : encodeSigma C = bs := by
  unfold decodeSigma at h
  split at h
  · exact absurd h (by simp)
  · rename_i n r hr
    split at h
    · rename_i C' hC'
      split at h
      · rename_i hEq
        obtain rfl := Option.some.inj h
        exact hEq
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- The circuit encoding, as a `Computability.FinEncoding` over the alphabet `Bool`. -/
def circuitEncoding : Computability.FinEncoding ((n : ℕ) × Circuit n) where
  Γ := Bool
  encode := encodeSigma
  decode := decodeSigma
  decode_encode := decodeSigma_encodeSigma
  ΓFin := inferInstance

/-- The packaged encoding's `encode` field is `encodeSigma`. -/
theorem circuitEncoding_encode : circuitEncoding.encode = encodeSigma := rfl

/-- The packaged encoding's `decode` field is `decodeSigma`. -/
theorem circuitEncoding_decode : circuitEncoding.decode = decodeSigma := rfl

/-! ## CKT-SAT as a language -/

/-- CKT-SAT: the bit strings encoding a satisfiable circuit.  [AB09, Def 6.9] -/
def cktSatLang : Language Bool :=
  {w | ∃ C, decodeSigma w = some C ∧ C ∈ CktSat}

/-- `cktSatLang` and `BoolCircuit.CktSat` agree under the encoding. -/
theorem mem_cktSatLang_iff (C : (n : ℕ) × Circuit n) :
    encodeSigma C ∈ cktSatLang ↔ C ∈ CktSat := by
  constructor
  · rintro ⟨D, hD, hmem⟩
    rw [decodeSigma_encodeSigma C] at hD
    obtain rfl : C = D := Option.some.inj hD
    exact hmem
  · exact fun h => ⟨C, decodeSigma_encodeSigma C, h⟩

/-- `cktSatLang` is exactly the image of `CktSat` under the encoding. -/
theorem mem_cktSatLang_iff_exists (w : List Bool) :
    w ∈ cktSatLang ↔ ∃ C ∈ CktSat, encodeSigma C = w := by
  constructor
  · rintro ⟨C, hC, hmem⟩
    exact ⟨C, hmem, encodeSigma_of_decodeSigma hC⟩
  · rintro ⟨C, hmem, rfl⟩
    exact (mem_cktSatLang_iff C).mpr hmem

/-! Degenerate cases: zero inputs, the empty `AND` and the empty `OR`, a single
literal, and a string that encodes nothing. -/

example : encodeSigma ⟨0, .node true []⟩ = [false, true, true, false] := by
  simp [encodeSigma, encodeCircuit, unaryBits]

example : decodeSigma [false, true, true, false] = some ⟨0, .node true []⟩ := by
  simp [decodeSigma, readUnary, readCircuit, readChildren, encodeSigma, encodeCircuit, unaryBits]

example : encodeSigma ⟨0, .node true []⟩ ∈ cktSatLang :=
  (mem_cktSatLang_iff _).mpr ⟨finZeroElim, by simp [Circuit.eval]⟩

example : encodeSigma ⟨0, .node false []⟩ ∉ cktSatLang := by
  rw [mem_cktSatLang_iff]
  rintro ⟨u, hu⟩
  simp [Circuit.eval] at hu

example : encodeSigma ⟨1, .lit ⟨0, true⟩⟩ ∈ cktSatLang :=
  (mem_cktSatLang_iff _).mpr ⟨fun _ => true, by simp [Circuit.eval]⟩

example : ([] : List Bool) ∉ cktSatLang := by
  rintro ⟨C, hC, -⟩
  simp [decodeSigma, readUnary] at hC

/-! ## Clause count of the reduction to 3SAT -/

/-- No circuit is larger than its encoding is long.

**Proof sketch.** Structural induction.  A leaf has size one against an encoding
of at least three bits.  A gate's size is one plus the total size of its
children, and its encoding is two bits plus the children block; a side induction
on the list of children shows the children's total size is at most the block's
length, since each child contributes its own encoding and a continue bit. -/
theorem size_le_length_encodeCircuit {n : ℕ} (C : Circuit n) :
    C.size ≤ (encodeCircuit C).length := by
  induction C using Circuit.ind with
  | hlit l => simp [encodeCircuit, Circuit.size, unaryBits]
  | hnode b cs ih =>
      have hlist : ∀ ds : List (Circuit n), (∀ d ∈ ds, d.size ≤ (encodeCircuit d).length) →
          ds.foldr (fun d acc => d.size + acc) 0 ≤ (encodeChildren ds).length := by
        intro ds hds
        induction ds with
        | nil => simp [encodeChildren_nil]
        | cons d ds ihd =>
            have h1 := hds d List.mem_cons_self
            have h2 := ihd fun e he => hds e (List.mem_cons_of_mem _ he)
            rw [encodeChildren_cons]
            simp only [List.foldr_cons, List.length_cons, List.length_append]
            omega
      have hsum := hlist cs ih
      rw [encodeCircuit_node]
      simp only [Circuit.size, List.length_cons]
      omega

/-- An arity-tagged circuit's size never exceeds the length of its encoding. -/
theorem size_le_length_encodeSigma (C : (n : ℕ) × Circuit n) :
    C.2.size ≤ (encodeSigma C).length := by
  obtain ⟨n, C⟩ := C
  have h := size_le_length_encodeCircuit C
  simp only [encodeSigma, List.length_append, unaryBits, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

/-- One gate's clauses use `3` literal occurrences per child, plus one. -/
theorem gateClauses_flatten_length {n : ℕ} (b : Bool) (cs : List (Circuit n)) :
    (gateClauses b cs).flatten.length = 3 * cs.length + 1 := by
  have key : ∀ (x : Literal (CktVar n)) (g : Circuit n → Literal (CktVar n))
      (ds : List (Circuit n)), (ds.map fun c => [x, g c]).flatten.length = 2 * ds.length := by
    intro x g ds
    induction ds with
    | nil => simp
    | cons d ds ih => simp [ih]; omega
  cases b <;> simp [gateClauses, key] <;> omega

/-- The gate clauses of `C` use fewer than `7 * C.size` literal occurrences.

**Proof sketch.** Structural induction, in the same shape as
`BoolCircuit.Circuit.tseitin_length_lt`.  A leaf contributes four occurrences
against a size of one, and `7 - 3` is four.  At a gate the statement is
strengthened by three units of slack so that it survives the passage to the
children: a side induction on the list of children shows their occurrences,
*plus three per child*, still fit inside seven times their total size.  The
gate's own clauses cost three occurrences per child plus one, so those three per
child are exactly what the side induction set aside, and the gate's node itself
contributes the remaining seven units. -/
theorem tseitin_flatten_length_le {n : ℕ} (C : Circuit n) :
    C.tseitin.flatten.length + 3 ≤ 7 * C.size := by
  induction C using Circuit.ind with
  | hlit l => simp [Circuit.tseitin, Circuit.size]
  | hnode b cs ih =>
      have hlist : ∀ ds : List (Circuit n),
          (∀ d ∈ ds, d.tseitin.flatten.length + 3 ≤ 7 * d.size) →
          (ds.flatMap fun d => d.tseitin).flatten.length + 3 * ds.length ≤
            7 * ds.foldr (fun d acc => d.size + acc) 0 := by
        intro ds hds
        induction ds with
        | nil => simp
        | cons d ds ihd =>
            have h1 := hds d List.mem_cons_self
            have h2 := ihd fun e he => hds e (List.mem_cons_of_mem _ he)
            simp only [List.flatMap_cons, List.flatten_append, List.length_append,
              List.length_cons, List.foldr_cons]
            omega
      have hsum := hlist cs ih
      have hg := gateClauses_flatten_length b cs
      simp only [Circuit.tseitin, List.flatten_append, List.length_append, Circuit.size, hg]
      omega

/-- The CNF the reduction builds uses at most `7 * C.size` literal occurrences. -/
theorem toCNF_flatten_length_le {n : ℕ} (C : Circuit n) :
    C.toCNF.flatten.length ≤ 7 * C.size := by
  have h := tseitin_flatten_length_le C
  simp only [Circuit.toCNF, List.flatten_cons, List.length_append, List.length_cons,
    List.length_nil]
  omega

/-- The 3-CNF that [AB09, Lem 6.11] produces from a circuit has at most `13`
clauses per bit of the encoded circuit.

This is the clause-count half of the lemma and nothing more: it says how many
3-clauses come out, not how long they take to build, so it is not a `≤p`
statement.  AB gives no constant; `13` is this formalization's, read off the
clause counts above. -/
theorem length_to3SAT_toCNF_le (C : (n : ℕ) × Circuit n) :
    (to3SAT C.2.toCNF).length ≤ 13 * (encodeSigma C).length := by
  have h1 := SATTo3SAT.length_to3SAT_le C.2.toCNF
  have h2 := toCNF_flatten_length_le C.2
  have h3 := C.2.toCNF_length_le
  have h4 := size_le_length_encodeSigma C
  omega

end BoolCircuit

## ===== TCSlib/Complexity/CircuitComplexity/FeedForward.lean =====

/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Fin
import TCSlib.Complexity.CircuitComplexity.Basic

/-!
# Feedforward circuits

Layered DAG circuits over an arbitrary alphabet: `GateOp`/`Gate`/`FeedForward`,
evaluation (`evalNode`, `eval`, `eval₁`), the `size`/`Finite`/`onlyUsesGates`
measures, and `stdGateOps` — the standard unbounded fan-in gate set that
`Language.InSIZE` and `P/poly` are defined over.  The second half relates the
DAG model to the tree-shaped `BoolCircuit.Circuit` in both directions:
tree-unrolling (`FeedForward.toCircuit`, exponential in depth) and the
semantic wrapper `Circuit.toFeedForward`, which packages a tree's *evaluation*
as a single unrestricted first-layer gate — not a gate-level embedding; see
its docstring.

Written for the Razborov–Smolensky development
(`BooleanAnalysis/RazborovSmolensky/`) and relocated here as the shared
circuit model.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (Circuit basics: §6.1–6.2.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace BoolCircuit

/-- A single operation in a feedforward circuit. -/
structure GateOp (α : Type u) where
  ι : Type u
  func : (ι → α) → α

/-- A gate together with the wiring of its inputs. -/
structure Gate (α : Type u) (domain : Type v) where
  op : GateOp α
  inputs : op.ι → domain

/-- A layered feedforward circuit. Layer `0` is the input layer. -/
structure FeedForward (α : Type u) (inp : Type v) (out : Type v) where
  depth : ℕ
  nodes : Fin (depth + 1) → Type v
  gates : (d : Fin depth) → nodes d.succ → Gate α (nodes d.castSucc)
  nodes_zero : nodes 0 = inp
  nodes_last : nodes (Fin.last depth) = out

namespace FeedForward

attribute [simp] FeedForward.nodes_zero FeedForward.nodes_last

variable {α : Type u} {inp out : Type v}

/-- The identity gate. -/
abbrev GateOp.id (α : Type u) : GateOp α where
  ι := PUnit
  func x := x PUnit.unit

/-- Evaluate a single gate from the values on the previous layer. -/
def Gate.eval {domain : Type v} (g : Gate α domain) (xs : domain → α) : α :=
  g.op.func (xs ∘ g.inputs)

variable (F : FeedForward α inp out)

/-- Evaluate a node of a feedforward circuit. -/
def evalNode {d : Fin (F.depth + 1)} (node : F.nodes d) (xs : inp → α) : α :=
  let ⟨d, hd⟩ := d
  Nat.recAux
    (fun _ node' => xs (F.nodes_zero ▸ node'))
    (fun n ih hd node₀ =>
      Gate.eval (F.gates ⟨n, Nat.succ_lt_succ_iff.mp hd⟩ node₀) (ih _))
    d hd node

/-- Evaluate a circuit on an input. -/
def eval (xs : inp → α) : out → α :=
  fun o => F.evalNode (d := Fin.last F.depth) (F.nodes_last.symm.rec o) xs

/-- Evaluate a circuit with a unique output node. -/
def eval₁ [Unique out] (xs : inp → α) : α :=
  F.eval xs default

/-- The total number of non-input gates. -/
noncomputable def size : ℕ :=
  Nat.card (@Sigma (Fin F.depth) (fun d => F.nodes d.succ))

/-- Every layer is finite. -/
protected abbrev Finite : Prop :=
  ∀ i, Finite (F.nodes i)

/-- Every gate operation belongs to the given gate set. -/
def onlyUsesGates (S : Set (GateOp α)) : Prop :=
  ∀ d u, (F.gates d u).op ∈ S

end FeedForward

/-! ### The standard gate set -/

/-- The standard unbounded fan-in gate set — identity, NOT, and unbounded AND.
This is the basis `Language.InSIZE` and `P/poly` are defined over; it is also
the gate set of plain `AC⁰` circuits, and `RazborovSmolensky.ACp_GateOps`
extends it with `MOD p` gates. -/
def stdGateOps : Set (GateOp (Fin 2)) :=
  {FeedForward.GateOp.id (Fin 2),
   ⟨Fin 1, fun x ↦ 1 - x 0⟩} ∪
  ⋃ n, {⟨Fin n, fun x ↦ ∏ i, x i⟩}

/-!
## Conversion between FeedForward and BoolCircuit.Circuit

A `BoolCircuit.Circuit n` is **tree-shaped** (fanout ≤ 1 — each wire is used by exactly one
gate downstream).  A `FeedForward Bool (Fin n) out` is a **layered DAG** that permits
fanout > 1.  The two directions of conversion have different costs:

* **`FeedForward.toCircuit`** (DAG → tree, "tree-unrolling"): every node whose output
  is consumed by `k` downstream gates is duplicated `k` times.  If every gate has at most
  `f` input wires, the resulting tree has at most `(f + 1) ^ F.depth` nodes — an
  exponential blowup in depth.

* **`BoolCircuit.Circuit.toFeedForward`** (tree → DAG): a tree is already a DAG with
  fanout ≤ 1, so the embedding is faithful.  The FeedForward circuit has the same depth
  and its size is at most `C.size * C.depth` after inserting identity wires to pad
  shorter branches of an unbalanced tree to a uniform depth.
-/

section CircuitConversion

variable {n : ℕ} {out : Type}

/-! ### FeedForward Bool → BoolCircuit.Circuit (tree-unrolling) -/

/-- Predicate: every gate in `F` computes AND (when `isAnd d v = true`) or OR (when
    `isAnd d v = false`) of its inputs, as enumerated by `gfin`.  This is the gate
    restriction that makes a FeedForward circuit convertible into a `BoolCircuit.Circuit`. -/
def FeedForward.IsAndOrGate
    (F : FeedForward Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι) : Prop :=
  ∀ (d : Fin F.depth) (v : F.nodes d.succ) (xs : (F.gates d v).op.ι → Bool),
    haveI := gfin d v
    (F.gates d v).op.func xs =
      if isAnd d v then Finset.univ.val.toList.foldr (fun i acc => xs i && acc) true
      else Finset.univ.val.toList.foldr (fun i acc => xs i || acc) false

/-- Tree-unrolling: recursively expand node `v` at layer `m` into a `BoolCircuit.Circuit n`.
    Nodes used by multiple downstream gates are **duplicated**.
    * Layer-0 nodes (input variables) become positive literals.
    * Internal nodes become `Circuit.node` with one child subtree per input wire. -/
private noncomputable def nodeToCircuit
    (F : FeedForward Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι) :
    ∀ (m : ℕ) (hm : m < F.depth + 1), F.nodes ⟨m, hm⟩ → Circuit n :=
  Nat.recAux
    (fun _ v => .lit ⟨F.nodes_zero ▸ v, true⟩)
    (fun m ih hm v =>
      have hm' : m < F.depth := Nat.lt_of_succ_lt_succ hm
      haveI : Fintype (F.gates ⟨m, hm'⟩ v).op.ι := gfin ⟨m, hm'⟩ v
      .node (isAnd ⟨m, hm'⟩ v)
        (Finset.univ.val.toList.map fun i => ih _ ((F.gates ⟨m, hm'⟩ v).inputs i)))

/-- Tree-unrolled circuit evaluates identically to the original feedforward circuit. -/
theorem nodeToCircuit_eval
    (F : FeedForward Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι)
    (hcorrect : F.IsAndOrGate isAnd gfin)
    (m : ℕ) (hm : m < F.depth + 1) (v : F.nodes ⟨m, hm⟩) (x : Fin n → Bool) :
    (nodeToCircuit F isAnd gfin m hm v).eval x = F.evalNode v x := by
  induction m with
  | zero =>
    -- nodeToCircuit 0 = .lit ... by Nat.recAux_zero
    have h1 : nodeToCircuit F isAnd gfin 0 hm v = .lit ⟨F.nodes_zero ▸ v, true⟩ := by
      unfold nodeToCircuit; simp
    -- evalNode at d=0 = x (nodes_zero ▸ v) by Nat.recAux_zero
    have h2 : F.evalNode (d := ⟨0, hm⟩) v x = x (F.nodes_zero ▸ v) := by
      unfold FeedForward.evalNode; simp
    rw [h1, h2]; simp [Circuit.eval, Lit.eval]
  | succ m ih =>
    let hm' : m < F.depth := Nat.lt_of_succ_lt_succ hm
    let hm_lt : m < F.depth + 1 := Nat.lt_succ_of_lt hm'
    letI : Fintype (F.gates ⟨m, hm'⟩ v).op.ι := gfin ⟨m, hm'⟩ v
    -- nodeToCircuit (m+1) = .node ... by Nat.recAux_succ
    have h_node : nodeToCircuit F isAnd gfin (m + 1) hm v =
        .node (isAnd ⟨m, hm'⟩ v)
          (Finset.univ.val.toList.map fun i =>
            nodeToCircuit F isAnd gfin m hm_lt ((F.gates ⟨m, hm'⟩ v).inputs i)) := by
      unfold nodeToCircuit; rw [Nat.recAux_succ]
    -- evalNode at m+1 = Gate.eval (gate at m) ∘ evalNode at m
    have h_eval : F.evalNode (d := ⟨m + 1, hm⟩) v x =
        (F.gates ⟨m, hm'⟩ v).op.func
          (fun i => F.evalNode (d := ⟨m, hm_lt⟩) ((F.gates ⟨m, hm'⟩ v).inputs i) x) := by
      unfold FeedForward.evalNode; simp only []; rw [Nat.recAux_succ]
      simp only [FeedForward.Gate.eval]; rfl
    -- IH: each child's eval equals the corresponding evalNode
    have h_ih : ∀ i, (nodeToCircuit F isAnd gfin m hm_lt ((F.gates ⟨m, hm'⟩ v).inputs i)).eval x =
        F.evalNode (d := ⟨m, hm_lt⟩) ((F.gates ⟨m, hm'⟩ v).inputs i) x :=
      fun i => ih hm_lt ((F.gates ⟨m, hm'⟩ v).inputs i)
    rw [h_node, h_eval, hcorrect ⟨m, hm'⟩ v]
    cases isAnd ⟨m, hm'⟩ v <;> simp [Circuit.eval, List.foldr_map, h_ih]

/-
Size bound: tree-unrolled circuit at depth `m` has at most `(k + 1) ^ m` nodes,
    where `k` bounds the fanin (number of input wires) of every gate.
-/
theorem nodeToCircuit_size_le
    (F : FeedForward Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι)
    {k : ℕ} (hk : ∀ (d : Fin F.depth) (v : F.nodes d.succ),
        Fintype.card (F.gates d v).op.ι ≤ k)
    (m : ℕ) (hm : m < F.depth + 1) (v : F.nodes ⟨m, hm⟩) :
    (nodeToCircuit F isAnd gfin m hm v).size ≤ (k + 1) ^ m := by
  revert hm v;
  induction' m with m ih;
  · intro hm v; unfold nodeToCircuit; simp +decide [ Circuit.size ] ;
  · intro hm v
    have h_node : (nodeToCircuit F isAnd gfin (m + 1) hm v).size = 1 + (Finset.univ.val.toList.map fun i => (nodeToCircuit F isAnd gfin m (Nat.lt_of_succ_lt hm) ((F.gates ⟨m, Nat.lt_of_succ_lt_succ hm⟩ v).inputs i)).size).foldr (fun c acc => c + acc) 0 := by
      unfold nodeToCircuit; simp +decide [ Nat.recAux ] ;
      unfold Circuit.size; simp +decide [ List.foldr_map ] ;
      congr! 2;
      congr! 2;
      exact Circuit.size.eq_def _;
    have h_foldr : ∀ (L : List ℕ), (∀ c ∈ L, c ≤ (k + 1) ^ m) → L.foldr (fun c acc => c + acc) 0 ≤ L.length * (k + 1) ^ m := by
      intro L hL; induction L <;> simp_all +decide [ Nat.succ_mul ] ;
      grind;
    have := h_foldr ( List.map ( fun i => ( nodeToCircuit F isAnd gfin m ( Nat.lt_of_succ_lt hm ) ( ( F.gates ⟨ m, Nat.lt_of_succ_lt_succ hm ⟩ v ).inputs i ) ).size ) Finset.univ.val.toList ) ?_ <;> simp_all +decide [ pow_succ' ];
    · nlinarith [ hk ⟨ m, Nat.lt_of_succ_lt_succ hm ⟩ v, pow_pos ( Nat.succ_pos k ) m ];

namespace FeedForward

/-- Convert a FeedForward AND/OR circuit to a `BoolCircuit.Circuit` by tree-unrolling.
    The output node `o : out` selects which single-bit output to expand.
    Shared nodes are duplicated; the resulting circuit has size ≤ `(k + 1) ^ F.depth`
    when every gate has at most `k` input wires. -/
noncomputable def toCircuit
    (F : FeedForward Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι)
    (o : out) : Circuit n :=
  nodeToCircuit F isAnd gfin F.depth (Fin.last F.depth).isLt (F.nodes_last.symm.rec o)

/-- Tree-unrolling preserves evaluation: `F.toCircuit isAnd gfin o` computes
`F.eval x o`. -/
theorem toCircuit_eval
    (F : FeedForward Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι)
    (hcorrect : F.IsAndOrGate isAnd gfin)
    (o : out) (x : Fin n → Bool) :
    (F.toCircuit isAnd gfin o).eval x = F.eval x o := by
  simp only [toCircuit, eval]
  exact nodeToCircuit_eval F isAnd gfin hcorrect _ _ _ x

/-- The tree-unrolled circuit has size at most `(k + 1) ^ F.depth` when every
gate reads at most `k` wires. -/
theorem toCircuit_size_le
    (F : FeedForward Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι)
    {k : ℕ} (hk : ∀ (d : Fin F.depth) (v : F.nodes d.succ),
        Fintype.card (F.gates d v).op.ι ≤ k)
    (o : out) :
    (F.toCircuit isAnd gfin o).size ≤ (k + 1) ^ F.depth :=
  nodeToCircuit_size_le F isAnd gfin hk F.depth _ _

end FeedForward

/-! ### BoolCircuit.Circuit → FeedForward Bool (semantic wrapper) -/

-- Layer 0 is the input layer (Fin n); all other layers carry Unit (single output wire).
-- The gate at layer 0 computes C.eval from all inputs at once; gates at layers 1..depth
-- are identity wires that pass the single Bool value upward unchanged.
/-- Package a `BoolCircuit.Circuit n` as a `FeedForward Bool (Fin n) Unit` — a
    **semantic wrapper, not a gate-level embedding**: the single layer-0 gate is
    the unrestricted operation `⟨Fin n, C.eval⟩` and every later layer is one
    identity wire, so `size = depth = C.depth + 1` whatever `C.size` is.  The
    source gates are not embedded, no branch is padded, and the first gate is in
    general **not** in `stdGateOps`, so this map can never discharge an
    `OnlyUsesGates` obligation — a future machine-to-circuit bridge must build
    its family gate by gate instead.  Only evaluation is preserved
    (`Circuit.toFeedForward_eval`). -/
noncomputable def _root_.BoolCircuit.Circuit.toFeedForward (C : Circuit n) : FeedForward Bool (Fin n) Unit where
  depth := C.depth + 1
  nodes d := if d.val = 0 then Fin n else Unit
  gates d _ :=
    if h : d.val = 0 then
      -- Layer 0 → 1: compute C.eval from the input layer
      let h' : d.castSucc.val = 0 := h  -- castSucc preserves val
      let hdom : (if d.castSucc.val = 0 then Fin n else Unit) = Fin n := if_pos h'
      { op := { ι := Fin n, func := C.eval }
        inputs := Eq.mpr hdom }
    else
      -- Layer d > 0 → d+1: identity wire
      let h' : d.castSucc.val ≠ 0 := h  -- castSucc preserves val
      let hdom : (if d.castSucc.val = 0 then Fin n else Unit) = Unit := if_neg h'
      { op := FeedForward.GateOp.id Bool
        inputs := fun _ => Eq.mpr hdom () }
  nodes_zero := if_pos rfl
  nodes_last := by
    show (if (Fin.last (C.depth + 1)).val = 0 then Fin n else Unit) = Unit
    rw [Fin.val_last]; exact if_neg (Nat.succ_ne_zero C.depth)

/-
Every non-input layer node of `C.toFeedForward` evaluates to `C.eval x`.
    Layer 1 applies the `C.eval` gate to the inputs; higher layers are identity wires.
-/
private theorem Circuit.toFeedForward_evalNode_const (C : Circuit n) (x : Fin n → Bool)
    (m : ℕ) (hm : m < C.depth + 1 + 1) (hpos : 0 < m)
    (v : C.toFeedForward.nodes ⟨m, hm⟩) :
    C.toFeedForward.evalNode (d := ⟨m, hm⟩) v x = C.eval x := by
  rcases m with ( _ | m ) <;> simp_all +decide;
  induction' m with m ih;
  · congr! 1;
  · convert ih ( Nat.lt_of_succ_lt hm ) _ using 1

/-- The embedded feedforward circuit evaluates identically to the original `Circuit`.
    Proof: evalNode traces backward through identity gates at layers 1..depth, then
    the layer-0 C.eval gate computes C.eval xs from the input layer. -/
theorem Circuit.toFeedForward_eval (C : Circuit n) (x : Fin n → Bool) :
    C.toFeedForward.eval₁ x = C.eval x := by
  convert Circuit.toFeedForward_evalNode_const C x ( C.toFeedForward.depth ) ( by simp +decide [ Circuit.toFeedForward ] ) ( by simp +decide [ Circuit.toFeedForward ] ) _

/-- The embedding uses one extra layer for the input, so depth is C.depth + 1. -/
theorem Circuit.toFeedForward_depth (C : Circuit n) :
    C.toFeedForward.depth = C.depth + 1 := rfl

/-
The embedded feedforward circuit has size ≤ C.size * (C.depth + 1).
    Its size equals C.depth + 1 (one Unit gate per layer), and C.size ≥ 1.
-/
theorem Circuit.toFeedForward_size_le (C : Circuit n) :
    C.toFeedForward.size ≤ C.size * (C.depth + 1) := by
  refine' le_trans _ ( Nat.le_mul_of_pos_left _ <| BoolCircuit.Circuit.one_le_size C );
  unfold FeedForward.size;
  rw [ show C.toFeedForward.nodes = fun d => if d.val = 0 then Fin n else Unit from funext fun x => by cases x; rfl ] ; simp +decide;
  exact Nat.le_refl C.toFeedForward.depth

end CircuitConversion

end BoolCircuit

## ===== TCSlib/Complexity/CircuitComplexity/HardFunctions.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Card
import TCSlib.Complexity.CircuitComplexity.Encoding

/-!
# Existence of hard Boolean functions

Arora–Barak's counting argument: there are more Boolean functions on `n` bits than
there are small circuits, so some function is computed by none of them.

## Main definitions

None — this file adds only theorems, over `BoolCircuit.Circuit` and `BoolCircuit.encodeCircuit`.

## Main results

* `BoolCircuit.length_encodeCircuit_succ_le` — a circuit of size `S` on `n` variables has an
  encoding of fewer than `(n + 4) * S` bits.
* `BoolCircuit.encodeCircuit_injective` — distinct circuits have distinct encodings.
* `BoolCircuit.card_computable_le` — at most `2 ^ ((n + 4) * S)` functions
  `(Fin n → Bool) → Bool` are computed by a circuit of size at most `S`.
* `BoolCircuit.exists_not_eval_of_lt` — whenever `(n + 4) * S < 2 ^ n`, some function
  differs from every size-`≤ S` circuit at some input.  [AB09, Thm 6.21]
* `BoolCircuit.exists_hard_function` — the same with the explicit size bound
  `2 ^ n / (n + 5)`.  [AB09, Thm 6.21]

## Divergences from [AB09, Thm 6.21]

**AB's size bound `2 ^ n / (10 n)` is not proved here, and the two statements are not
comparable.** [AB09, Def 6.1]'s circuit is a DAG whose `∨`/`∧` gates have fan-in `2`
and whose `¬` gates have fan-in `1`, with size its number of vertices — one source
vertex per input variable, however often that variable is read.
`BoolCircuit.Circuit` is a *tree* with unbounded fan-in and negation folded into its
literals, and `Circuit.size` counts every node. Two effects push our count up: every
literal *occurrence* costs a node, and no gate may be reused. One pushes it down:
`Circuit.size` charges `1` for a `k`-ary gate where Def 6.1 charges `k - 1` vertices.
A size-`S` tree embeds in a DAG on at most `S + 2 * n` vertices; in the other
direction only a depth-exponential unrolling is available, no polynomial bound.
Neither quantified statement implies the other on the strength of that
conversion: at `n = 20`, AB's cutoff `⌊2²⁰/200⌋ = 5242` transfers along
`S + 2n` only to tree cutoff `5202`, far below the `⌊2²⁰/25⌋ = 41943` proved
here, and tree hardness never rules out small DAGs with sharing.  AB's theorem
is about the more general model; this one has the larger cutoff in its narrower
one — and the families are not nested at every `S`: the three-literal `AND` on `n = 3` has
`Circuit.size = 4`, whereas Def 6.1 needs at least `5` vertices for that function, so
at `S = 4` AB's family is empty and ours is not. Neither comparison is formalized;
both describe the gap to AB, not anything proved below.

The bound proved is `(n + 4) * S < 2 ^ n`, i.e. hardness at size `2 ^ n / (n + 5)`.
It comes from `Encoding.lean`'s serialiser: a leaf costs `idx + 3` bits, its index
being written in unary, and a gate costs three bits plus one per child, so size `S`
fits in fewer than `(n + 4) * S` bits, against the `9 · S · log S` AB cites for an
adjacency list. Since `n + 5 < 10 n` for `n ≥ 1`, `2 ^ n / (n + 5)` is the larger of
the two numbers — a unary index costs `n` bits a leaf, the same order as AB's
`log S ≈ n`, against AB's generous constant `9`. That is not a strengthening of AB: it
is a weaker statement that happens to admit a larger constant. `n + 3` would close for
every `n ≥ 1` — only `n = 0`, where `.node b []` meets `(n + 4) * 1` with equality,
forces the `4` — but carrying `0 < n` through every downstream statement to move the
denominator from `n + 5` to `n + 4` buys nothing.

`n > 1` is not assumed. `(n + 4) * S < 2 ^ n` forces `S = 0` for `n ≤ 2`, and
`Circuit.size` is never `0`, so the conclusion is vacuous there; it first has content
at `n = 3`. AB's own `2 ^ n / (10 n)` is below `1` until `n = 6`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

/-! ## Bit strings as numbers -/

/-- A bit string as a number: its bits, terminated by a `1` so that the length is
recoverable. -/
private def bitsToNat (w : List Bool) : ℕ :=
  Nat.ofDigits 2 ((w.map fun b => if b then 1 else 0) ++ [1])

/-- Every digit of `bitsToNat`'s digit list is `0` or `1`. -/
private theorem bitsToNat_digits_lt (w : List Bool) :
    ∀ d ∈ (w.map fun b => if b then 1 else 0) ++ [1], d < 2 := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · obtain ⟨b, -, rfl⟩ := List.mem_map.mp hd
    cases b <;> norm_num
  · simp only [List.mem_singleton] at hd
    omega

/-- A string of `k` bits codes a number below `2 ^ (k + 1)`. -/
private theorem bitsToNat_lt (w : List Bool) : bitsToNat w < 2 ^ (w.length + 1) := by
  have h := Nat.ofDigits_lt_base_pow_length (b := 2) (by norm_num) (bitsToNat_digits_lt w)
  simpa [bitsToNat] using h

/-- Distinct bit strings code distinct numbers. -/
private theorem bitsToNat_injective : Function.Injective bitsToNat := by
  have key : ∀ w : List Bool,
      Nat.digits 2 (bitsToNat w) = (w.map fun b => if b then 1 else 0) ++ [1] := by
    intro w
    refine Nat.digits_ofDigits 2 (by norm_num) _ (bitsToNat_digits_lt w) ?_
    intro hne
    rw [List.getLast_append_singleton]
    omega
  intro w₁ w₂ h
  have h₂ : (w₁.map fun b => if b then 1 else 0) ++ [1]
      = (w₂.map fun b => if b then 1 else 0) ++ [1] := by
    rw [← key w₁, ← key w₂, h]
  have hf : Function.Injective (fun b : Bool => if b then 1 else 0) := by decide
  exact List.map_injective_iff.mpr hf (List.append_cancel_right h₂)

/-! ## How long a circuit's encoding is -/

/-- A literal's encoding is `idx + 3` bits: a tag bit, a sign bit, and the index
in unary. -/
private theorem length_encodeCircuit_lit {n : ℕ} :
    ∀ (k : ℕ) (h : k < n) (s : Bool),
      (encodeCircuit (Circuit.lit (n := n) ⟨⟨k, h⟩, s⟩)).length = k + 3
  | 0, _, _ => by simp only [encodeCircuit]; rfl
  | k + 1, h, s => by
      have h' : k < n := Nat.lt_of_succ_lt h
      have step : (encodeCircuit (Circuit.lit (n := n) ⟨⟨k + 1, h⟩, s⟩)).length
          = (encodeCircuit (Circuit.lit (n := n) ⟨⟨k, h'⟩, s⟩)).length + 1 := by
        simp only [encodeCircuit]; rfl
      rw [step, length_encodeCircuit_lit k h' s]

/-- A circuit of size `S` on `n` variables encodes into fewer than `(n + 4) * S` bits.

**Proof sketch.** Structural induction. A leaf's encoding is a tag bit, a sign bit and
its variable index in unary, so `idx + 3 < n + 4` bits against a size of one. A gate's
encoding is a tag bit, a connective bit and its children block, the block being one
continue bit per child, the children's own encodings, and a stop bit; a side induction
on the list of children shows the block is at most `(n + 4)` times the children's total
size, plus one — each child pays for its own continue bit out of the one bit of slack
the statement carries. The gate's two tag bits, its stop bit and that slack come to
four bits, which is at most the `n + 4` the gate's own node contributes. -/
theorem length_encodeCircuit_succ_le {n : ℕ} (C : Circuit n) :
    (encodeCircuit C).length + 1 ≤ (n + 4) * C.size := by
  induction C using Circuit.ind with
  | hlit l =>
      obtain ⟨⟨k, hk⟩, s⟩ := l
      rw [length_encodeCircuit_lit k hk s]
      simp only [Circuit.size, Nat.mul_one]
      omega
  | hnode b cs ih =>
      have hlist : ∀ ds : List (Circuit n),
          (∀ d ∈ ds, (encodeCircuit d).length + 1 ≤ (n + 4) * d.size) →
          (encodeChildren ds).length ≤
            (n + 4) * ds.foldr (fun d acc => d.size + acc) 0 + 1 := by
        intro ds hds
        induction ds with
        | nil => simp [encodeChildren_nil]
        | cons d ds ihd =>
            have h1 := hds d List.mem_cons_self
            have h2 := ihd fun e he => hds e (List.mem_cons_of_mem _ he)
            rw [encodeChildren_cons]
            simp only [List.length_cons, List.length_append, List.foldr_cons, Nat.mul_add]
            omega
      have hsum := hlist cs ih
      rw [encodeCircuit_node]
      simp only [List.length_cons, Circuit.size, Nat.mul_add, Nat.mul_one]
      omega

/-- Distinct circuits have distinct encodings. -/
theorem encodeCircuit_injective {n : ℕ} : Function.Injective (encodeCircuit (n := n)) := by
  intro C D h
  have hC := readCircuit_encodeCircuit C (encodeCircuit C).length [] le_rfl
  have hD := readCircuit_encodeCircuit D (encodeCircuit D).length [] le_rfl
  rw [List.append_nil] at hC hD
  rw [h] at hC
  simpa using hC.symm.trans hD

/-! ## The counting argument -/

/-- At most `2 ^ ((n + 4) * S)` Boolean functions on `n` variables are computed by a
circuit of size at most `S`.  [AB09, Thm 6.21]

**Proof sketch.** Pick, for each function in the set, a circuit of size at most `S`
computing it, and send the function to the number coding that circuit's encoding. The
map is injective on the set: the code determines the bit string, the bit string
determines the circuit, and the circuit determines the function it computes. Its values
lie below `2 ^ ((n + 4) * S)`, because a circuit of size at most `S` encodes into fewer
than `(n + 4) * S` bits. -/
theorem card_computable_le (n S : ℕ) :
    {f : (Fin n → Bool) → Bool | ∃ C : Circuit n, C.size ≤ S ∧ C.eval = f}.ncard
      ≤ 2 ^ ((n + 4) * S) := by
  classical
  haveI : Nonempty (Circuit n) := ⟨Circuit.node true []⟩
  have key : ∀ f ∈ {f : (Fin n → Bool) → Bool | ∃ C : Circuit n, C.size ≤ S ∧ C.eval = f},
      ∃ C : Circuit n, C.size ≤ S ∧ C.eval = f := fun _ hf => hf
  choose! g hg₁ hg₂ using key
  have hmain := Set.ncard_le_ncard_of_injOn
    (t := (↑(Finset.range (2 ^ ((n + 4) * S))) : Set ℕ))
    (fun f => bitsToNat (encodeCircuit (g f)))
    (fun f hf => by
      simp only [Finset.coe_range, Set.mem_Iio]
      calc bitsToNat (encodeCircuit (g f)) < 2 ^ ((encodeCircuit (g f)).length + 1) :=
            bitsToNat_lt _
        _ ≤ 2 ^ ((n + 4) * S) :=
            Nat.pow_le_pow_right (by norm_num)
              (le_trans (length_encodeCircuit_succ_le (g f))
                (Nat.mul_le_mul_left _ (hg₁ f hf))))
    (fun f₁ h₁ f₂ h₂ heq => by
      have hg : g f₁ = g f₂ := encodeCircuit_injective (bitsToNat_injective heq)
      rw [← hg₂ f₁ h₁, ← hg₂ f₂ h₂, hg])
    (Finset.finite_toSet _)
  rwa [Set.ncard_coe_finset, Finset.card_range] at hmain

/-- Some Boolean function on `n` variables differs, at some input, from every circuit of
size at most `S`, whenever `(n + 4) * S < 2 ^ n`.  [AB09, Thm 6.21]

**Proof sketch.** There are `2 ^ 2 ^ n` functions on `n` variables and, by
`card_computable_le`, at most `2 ^ ((n + 4) * S)` of them are computed by a circuit of
size at most `S`; the hypothesis makes the second number the smaller, so the computable
ones are not all of them. A function outside that set is computed by no such circuit,
and two Boolean functions that are not equal differ at a point. -/
theorem exists_not_eval_of_lt {n S : ℕ} (h : (n + 4) * S < 2 ^ n) :
    ∃ f : (Fin n → Bool) → Bool, ∀ C : Circuit n, C.size ≤ S → ∃ x, C.eval x ≠ f x := by
  classical
  set T : Set ((Fin n → Bool) → Bool) :=
    {f | ∃ C : Circuit n, C.size ≤ S ∧ C.eval = f}
  have hcard : T.ncard ≤ 2 ^ ((n + 4) * S) := card_computable_le n S
  have hcardF : Nat.card ((Fin n → Bool) → Bool) = 2 ^ 2 ^ n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun]
    simp
  obtain ⟨f, hf⟩ : ∃ f : (Fin n → Bool) → Bool, f ∉ T := by
    by_contra hcon
    push_neg at hcon
    rw [Set.eq_univ_of_forall hcon, Set.ncard_univ, hcardF] at hcard
    exact absurd (lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) h) hcard) (lt_irrefl _)
  refine ⟨f, fun C hC => ?_⟩
  by_contra hcon
  push_neg at hcon
  exact hf ⟨C, hC, funext hcon⟩

/-- For every `n` there is a Boolean function on `n` variables that no circuit of size
at most `2 ^ n / (n + 5)` computes.  [AB09, Thm 6.21]

**Proof sketch.** Immediate from `exists_not_eval_of_lt`: if `2 ^ n / (n + 5)` is zero
the hypothesis is `0 < 2 ^ n`, and otherwise multiplying it by `n + 4` rather than
`n + 5` strictly decreases the product, which `n + 5` times the quotient already keeps
below `2 ^ n`. -/
theorem exists_hard_function (n : ℕ) :
    ∃ f : (Fin n → Bool) → Bool,
      ∀ C : Circuit n, C.size ≤ 2 ^ n / (n + 5) → ∃ x, C.eval x ≠ f x := by
  refine exists_not_eval_of_lt ?_
  rcases Nat.eq_zero_or_pos (2 ^ n / (n + 5)) with hq | hq
  · rw [hq, Nat.mul_zero]
    exact Nat.pow_pos (by norm_num)
  · calc (n + 4) * (2 ^ n / (n + 5)) < (n + 5) * (2 ^ n / (n + 5)) :=
          (Nat.mul_lt_mul_right hq).mpr (by omega)
      _ = 2 ^ n / (n + 5) * (n + 5) := Nat.mul_comm _ _
      _ ≤ 2 ^ n := Nat.div_mul_le_self _ _

/-! Degenerate arities. `Circuit.size` is never `0` and `2 ^ n / (n + 5)` is `0` for
`n ≤ 2`, so `exists_hard_function` says nothing below `n = 3`; at `n = 3` it excludes
every literal and both empty gates. -/

example (C : Circuit 2) : ¬ C.size ≤ 2 ^ 2 / (2 + 5) := by
  cases C <;> simp [Circuit.size]

example : ∃ f : (Fin 3 → Bool) → Bool,
    ∀ C : Circuit 3, C.size ≤ 1 → ∃ x, C.eval x ≠ f x := by
  have h := exists_hard_function 3
  norm_num at h
  exact h

end BoolCircuit

## ===== TCSlib/Complexity/CircuitComplexity/Hierarchy.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.HardFunctions
import TCSlib.Complexity.CircuitComplexity.Universal

/-!
# A nonuniform size hierarchy for tree circuits

`Language.InTreeSize T` is the class of languages decided, at each input length `n`, by a
`BoolCircuit.Circuit n` of size at most `T n`.  **It is not `Language.InSIZE`**, and the
theorem below is therefore not [AB09, Thm 6.22]; see `## Divergences`.

## Main definitions

* `BoolCircuit.widenCircuit` / `BoolCircuit.restrictCircuit` — reindex a circuit into more variables, and
  restrict a circuit to its first `m` variables by fixing the rest to constants.
* `BoolCircuit.onFirst` — `f` applied to the first `m` of `n` input bits; [AB09, p.116]'s `g`.
* `Language.InTreeSize`, `BoolCircuit.TreeSize` — the size class, as a predicate and as a set.
* `BoolCircuit.padFamily` / `BoolCircuit.padLanguage` — the padded language and its circuits: at length `n`,
  `F n` applied to the first `ℓ n` bits.

## Main results

* `BoolCircuit.widenCircuit_size`, `BoolCircuit.restrictCircuit_size` — both reindexings preserve `size`
  exactly; `BoolCircuit.restrictCircuit_eval_of_onFirst` is the step [AB09, p.116] needs, pulling a
  circuit for `g` back to one for `f`.
* `Language.InTreeSize.mono`, `Language.zero_inTreeSize` — monotonicity in `T`, and that
  every class with `1 ≤ T` is inhabited.
* `BoolCircuit.padLanguage_inTreeSize` / `BoolCircuit.padLanguage_not_inTreeSize` — the two halves of the
  separation, from [AB09, Claim 2.13] and [AB09, Thm 6.21] respectively.
* `BoolCircuit.treeSize_ssubset` — `TreeSize T ⊂ TreeSize T'` given a padding length `ℓ`; the
  tree-model analogue of [AB09, Thm 6.22] and **not** that theorem, whose class is
  `Language.InSIZE`.
* `BoolCircuit.treeSize_ssubset_of_lt` — the same with `ℓ` supplied; `BoolCircuit.treeSize_one_ssubset` an
  instance of it, and `BoolCircuit.zero_mem_treeSize_one` that its smaller class is nonempty.

## Divergences from [AB09, Thm 6.22]

**This is not AB's `SIZE`, and AB's theorem is not formalized.** [AB09, Def 6.2]'s `SIZE(T)` is
rendered — with that file's declared divergences; it is **not** the same fixed
class (see `PPoly.lean`'s ledger) — by `Language.InSIZE`, over `BoolCircuit.CircuitFamily` — a layered `FeedForward`
*DAG* on `stdGateOps`.  Everything here is over `BoolCircuit.Circuit`, an unbounded-fan-in
*tree*.  Neither transfer is available.  Tree → `FeedForward` exists only as
`BoolCircuit.Circuit.toFeedForward`, which is over `FeedForward Bool`, not `Fin 2`, and puts
the whole circuit into one gate `⟨Fin n, C.eval⟩` that is not in `stdGateOps`; every layer
above the input is `Unit`, so its size is `C.depth + 1` whatever `C.size` is, and a map whose
image size never mentions its source's cannot transport a size class either way.
`FeedForward` → tree is `BoolCircuit.FeedForward.toCircuit`, correct only under
`FeedForward.IsAndOrGate` — every gate an AND or an OR — whereas `stdGateOps` also holds
`id` and `NOT`, for neither of which `BoolCircuit.Circuit` has a gate (it negates only at
literals); and its bound `(k + 1) ^ depth` is exponential in depth in any case.  Carrying
U10's hardness over to `SIZE`'s model needs that second direction, so the hierarchy is
stated here over the model U9 and U10 live in, and `SIZE(T) ⊊ SIZE(T')` remains open.

**The size measures also differ, in both directions.** `Circuit.size` counts every node of a
tree, so every literal *occurrence* costs a node and no gate can be reused, raising the count
against [AB09, Def 6.1]; but it charges `1` for a `k`-ary gate where Def 6.1 charges `k - 1`
vertices, lowering it.  The two families are therefore not comparable.  The full accounting
is in `Universal.lean` and `HardFunctions.lean`; it is not restated here.

**The constants are ours.** At [AB09, p.116] the padded function costs `10 ℓ 2 ^ ℓ` and the
hardness bound is `2 ^ ℓ / (10 ℓ)`; we use `Universal.lean`'s `2 ^ ℓ * (ℓ + 1) + 1` and
`HardFunctions.lean`'s side condition `(ℓ + 4) * S < 2 ^ ℓ`.  Both of ours are the sharper
number for every `ℓ ≥ 1`, which buys nothing across models — they measure the incomparable
object above.  AB's hypothesis `2ⁿ/n > T'(n) > 10 T(n) > n`, with `ℓ = 1.1 log n` chosen
inside the proof, is not reproduced: `ℓ` is a parameter here, constrained by `ℓ n ≤ n` and
the one inequality each half consumes.  Recovering AB's shape needs `Nat.log` arithmetic and
a large-`n` argument, and is not attempted.

**`ℓ n₀ ≥ 3` is what keeps the statement non-degenerate.** Below it `hlow` forces
`T n₀ = 0`, and `Circuit.size` is never `0`, so `TreeSize T` would be empty and the strict
inclusion would separate nothing.  `BoolCircuit.treeSize_one_ssubset` takes `ℓ n = min n 3`.

**One length suffices.** AB relates `T` and `T'` at every length; `hlow` is imposed here at a
single `n₀`, which is all strictness needs.  Demanding it at every `n` would force `T n = 0`
for `n ≤ 2` and empty the class, for the reason just given.

## Implementation notes

`BoolCircuit.TreeCircuitFamily` in `NCAC.lean` bundles the same `(n : ℕ) → Circuit n` data,
but that file is a parallel track; `Language.InTreeSize` quantifies over the bare function so
that this file depends only on U9 and U10.  Merging the two is a cross-track item.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {m n : ℕ}

/-! ## Reindexing a circuit -/

/-- An empty gate is a constant: the empty `AND` is `true`, the empty `OR` is `false`. -/
theorem eval_node_nil (b : Bool) (x : Fin n → Bool) :
    (Circuit.node b ([] : List (Circuit n))).eval x = b := by
  cases b <;> simp [Circuit.eval]

/-- A circuit on `m` variables read as a circuit on `n ≥ m` variables, ignoring the rest. -/
def widenCircuit (h : m ≤ n) : Circuit m → Circuit n
  | .lit l => .lit ⟨Fin.castLE h l.idx, l.sign⟩
  | .node b cs => .node b (cs.map (widenCircuit h))

/-- Widening reads the first `m` coordinates of its input. -/
theorem widenCircuit_eval (h : m ≤ n) (c : Circuit m) (x : Fin n → Bool) :
    (widenCircuit h c).eval x = c.eval fun i => x (Fin.castLE h i) := by
  induction c using Circuit.ind with
  | hlit l => simp [widenCircuit, Circuit.eval, Lit.eval]
  | hnode b cs ih =>
      cases b <;>
        simp only [widenCircuit, Circuit.eval, List.foldr_map] <;>
        exact List.foldr_ext _ _ _ fun c hc _ => by rw [ih c hc]

/-- Widening changes no node. -/
theorem widenCircuit_size (h : m ≤ n) (c : Circuit m) :
    (widenCircuit h c).size = c.size := by
  induction c using Circuit.ind with
  | hlit l => simp [widenCircuit, Circuit.size]
  | hnode b cs ih =>
      simp only [widenCircuit, Circuit.size, List.foldr_map]
      exact congrArg (1 + ·) (List.foldr_ext _ _ _ fun c hc _ => by rw [ih c hc])

/-- The input on `n` variables agreeing with `y` on the first `m` and with `pad` beyond. -/
def extendBy (m : ℕ) (pad : Fin n → Bool) (y : Fin m → Bool) : Fin n → Bool :=
  fun i => if hi : i.val < m then y ⟨i.val, hi⟩ else pad i

/-- A circuit on `n` variables restricted to its first `m`, the rest fixed to `pad`.  A
literal on a fixed variable becomes an empty gate, which costs the same one node. -/
def restrictCircuit (m : ℕ) (pad : Fin n → Bool) : Circuit n → Circuit m
  | .lit l =>
      if hi : l.idx.val < m then .lit ⟨⟨l.idx.val, hi⟩, l.sign⟩ else .node (l.eval pad) []
  | .node b cs => .node b (cs.map (restrictCircuit m pad))

/-- Restricting computes the original circuit on the extended input. -/
theorem restrictCircuit_eval (m : ℕ) (pad : Fin n → Bool) (c : Circuit n) (y : Fin m → Bool) :
    (restrictCircuit m pad c).eval y = c.eval (extendBy m pad y) := by
  induction c using Circuit.ind with
  | hlit l =>
      by_cases hi : l.idx.val < m
      · simp [restrictCircuit, hi, Circuit.eval, Lit.eval, extendBy]
      · simp [restrictCircuit, hi, eval_node_nil, Circuit.eval, Lit.eval, extendBy]
  | hnode b cs ih =>
      cases b <;>
        simp only [restrictCircuit, Circuit.eval, List.foldr_map] <;>
        exact List.foldr_ext _ _ _ fun c hc _ => by rw [ih c hc]

/-- Restricting changes no node: a fixed literal becomes a one-node empty gate. -/
theorem restrictCircuit_size (m : ℕ) (pad : Fin n → Bool) (c : Circuit n) :
    (restrictCircuit m pad c).size = c.size := by
  induction c using Circuit.ind with
  | hlit l => by_cases hi : l.idx.val < m <;> simp [restrictCircuit, hi, Circuit.size]
  | hnode b cs ih =>
      simp only [restrictCircuit, Circuit.size, List.foldr_map]
      exact congrArg (1 + ·) (List.foldr_ext _ _ _ fun c hc _ => by rw [ih c hc])

/-- `f` applied to the first `m` of `n` input bits.  [AB09, p.116]'s `g`. -/
def onFirst (h : m ≤ n) (f : (Fin m → Bool) → Bool) : (Fin n → Bool) → Bool :=
  fun x => f fun i => x (Fin.castLE h i)

/-- A circuit for `onFirst h f` restricts to a circuit for `f`. -/
theorem restrictCircuit_eval_of_onFirst {h : m ≤ n} {pad : Fin n → Bool} {c : Circuit n}
    {f : (Fin m → Bool) → Bool} (hc : ∀ x, c.eval x = onFirst h f x) (y : Fin m → Bool) :
    (restrictCircuit m pad c).eval y = f y := by
  rw [restrictCircuit_eval, hc, onFirst]
  exact congrArg f (funext fun i => by simp [extendBy, Fin.castLE])

end BoolCircuit

/-! ## The size class -/

/-- `L ∈ TreeSize(T)`: some family of `BoolCircuit.Circuit`s, the length-`n` one of size at
most `T n`, decides `L`.  **Not** [AB09, Def 6.2] — see this file's `## Divergences`. -/
def Language.InTreeSize (T : ℕ → ℕ) (L : Language Bool) : Prop :=
  ∃ C : (n : ℕ) → BoolCircuit.Circuit n,
    (∀ n, (C n).size ≤ T n) ∧ ∀ w : List Bool, w ∈ L ↔ (C w.length).eval w.get = true

/-- `TreeSize(T) ⊆ TreeSize(T')` whenever `T ≤ T'` pointwise. -/
theorem Language.InTreeSize.mono {T T' : ℕ → ℕ} {L : Language Bool} (hL : L.InTreeSize T)
    (h : ∀ n, T n ≤ T' n) : L.InTreeSize T' := by
  obtain ⟨C, hS, hC⟩ := hL
  exact ⟨C, fun n => (hS n).trans (h n), hC⟩

/-- The empty language needs only the empty `OR`, so every class with `1 ≤ T` is inhabited. -/
theorem Language.zero_inTreeSize {T : ℕ → ℕ} (hT : ∀ n, 1 ≤ T n) :
    (0 : Language Bool).InTreeSize T :=
  ⟨fun _ => .node false [], fun n => by simpa [BoolCircuit.Circuit.size] using hT n, fun w => by
    simp only [BoolCircuit.eval_node_nil, Bool.false_eq_true, iff_false]
    exact Language.notMem_zero w⟩

namespace BoolCircuit

variable {m n : ℕ}

/-- The size class packaged as a set of languages. -/
def TreeSize (T : ℕ → ℕ) : Set (Language Bool) := {L | L.InTreeSize T}

/-- Set membership in `TreeSize` agrees with the predicate `Language.InTreeSize`. -/
@[simp]
theorem mem_treeSize_iff (T : ℕ → ℕ) (L : Language Bool) :
    L ∈ TreeSize T ↔ L.InTreeSize T :=
  Iff.rfl

/-- Two families deciding the same language agree on every assignment.  Every assignment is a
`w.get` for `w = List.ofFn x`; `key` generalizes the length so that reaching it is a `subst`
rather than a dependent rewrite. -/
private theorem eval_eq_of_iff {C D : (n : ℕ) → Circuit n}
    (h : ∀ w : List Bool, (C w.length).eval w.get = true ↔ (D w.length).eval w.get = true)
    (n : ℕ) (x : Fin n → Bool) : (C n).eval x = (D n).eval x := by
  have hall : ∀ w : List Bool, (C w.length).eval w.get = (D w.length).eval w.get := fun w => by
    rw [Bool.eq_iff_iff]; exact h w
  have key : ∀ (k : ℕ) (w : List Bool) (hw : w.length = k) (z : Fin k → Bool),
      (∀ i, z i = w.get (Fin.cast hw.symm i)) → (C k).eval z = (D k).eval z := by
    intro k w hw z hz
    subst hw
    have hzw : z = w.get := funext fun i => by simpa using hz i
    subst hzw
    exact hall w
  exact key n (List.ofFn x) List.length_ofFn x fun i => by simp

/-! ## Padding a hard function -/

/-- The circuit family of [AB09, p.116]: at length `n`, the universal circuit for `F n`
widened to read only the first `ℓ n` bits. -/
noncomputable def padFamily {ℓ : ℕ → ℕ} (hle : ∀ n, ℓ n ≤ n)
    (F : (n : ℕ) → (Fin (ℓ n) → Bool) → Bool) (n : ℕ) : Circuit n :=
  widenCircuit (hle n) (universalCircuit (F n))

/-- `padFamily` computes `F n` on the first `ℓ n` bits. -/
theorem padFamily_eval {ℓ : ℕ → ℕ} (hle : ∀ n, ℓ n ≤ n)
    (F : (n : ℕ) → (Fin (ℓ n) → Bool) → Bool) (n : ℕ) (x : Fin n → Bool) :
    (padFamily hle F n).eval x = onFirst (hle n) (F n) x := by
  rw [padFamily, widenCircuit_eval, onFirst, universalCircuit_eval]

/-- The language `padFamily` decides. -/
def padLanguage {ℓ : ℕ → ℕ} (hle : ∀ n, ℓ n ≤ n)
    (F : (n : ℕ) → (Fin (ℓ n) → Bool) → Bool) : Language Bool :=
  {w | (padFamily hle F w.length).eval w.get = true}

/-- The upper half: padding costs nothing, so [AB09, Claim 2.13]'s bound at length `ℓ n`
bounds the circuit at length `n`. -/
theorem padLanguage_inTreeSize {ℓ T' : ℕ → ℕ} (hle : ∀ n, ℓ n ≤ n)
    (F : (n : ℕ) → (Fin (ℓ n) → Bool) → Bool)
    (hup : ∀ n, 2 ^ ℓ n * (ℓ n + 1) + 1 ≤ T' n) :
    (padLanguage hle F).InTreeSize T' :=
  ⟨padFamily hle F, fun n => by
    rw [padFamily, widenCircuit_size]
    exact (universalCircuit_size_le (F n)).trans (hup n), fun _ => Iff.rfl⟩

/-- The lower half: if `F n₀` is hard for size `T n₀`, the padded language is not in
`TreeSize(T)`.

**Proof sketch.** A family deciding `padLanguage` agrees with `padFamily` on every word,
hence — by `eval_eq_of_iff` — on every assignment, so at length `n₀` its circuit computes
`F n₀` on the first `ℓ n₀` bits.  Restricting that circuit to its first `ℓ n₀` variables,
with the rest fixed to `false`, gives a circuit for `F n₀` itself of the same size, which
hardness forbids. -/
theorem padLanguage_not_inTreeSize {ℓ T : ℕ → ℕ} {n₀ : ℕ} (hle : ∀ n, ℓ n ≤ n)
    (F : (n : ℕ) → (Fin (ℓ n) → Bool) → Bool)
    (hF : ∀ C : Circuit (ℓ n₀), C.size ≤ T n₀ → ∃ x, C.eval x ≠ F n₀ x) :
    ¬ (padLanguage hle F).InTreeSize T := by
  rintro ⟨D, hDsize, hDL⟩
  have hev : ∀ x : Fin n₀ → Bool, (D n₀).eval x = onFirst (hle n₀) (F n₀) x := fun x => by
    rw [← eval_eq_of_iff (fun w => hDL w) n₀ x, padFamily_eval]
  obtain ⟨y, hy⟩ := hF (restrictCircuit (ℓ n₀) (fun _ => false) (D n₀))
    (by rw [restrictCircuit_size]; exact hDsize n₀)
  exact hy (restrictCircuit_eval_of_onFirst hev y)

/-! ## The hierarchy -/

/-- **Nonuniform hierarchy, tree model.**  With a padding length `ℓ` long enough that
[AB09, Thm 6.21] bites at some length `n₀` and short enough that [AB09, Claim 2.13] still
fits inside `T'`, `TreeSize(T)` is a proper subclass of `TreeSize(T')`.  The tree-model analogue
of [AB09, Thm 6.22]; not that theorem — see this file's `## Divergences`.

**Proof sketch.** Inclusion is `Language.InTreeSize.mono`.  For strictness, pick at each
length `n` a function `F n` on `ℓ n` bits that no circuit of size `T n` computes, where the
counting bound permits one, and anything otherwise; `n₀` is a length where it permits one.
The language obtained by applying `F n` to the first `ℓ n` bits is in `TreeSize(T')` by
`padLanguage_inTreeSize` and outside `TreeSize(T)` by `padLanguage_not_inTreeSize`, so the
reverse inclusion fails. -/
theorem treeSize_ssubset {T T' ℓ : ℕ → ℕ} (n₀ : ℕ) (hle : ∀ n, ℓ n ≤ n)
    (hTT' : ∀ n, T n ≤ T' n) (hup : ∀ n, 2 ^ ℓ n * (ℓ n + 1) + 1 ≤ T' n)
    (hlow : (ℓ n₀ + 4) * T n₀ < 2 ^ ℓ n₀) :
    TreeSize T ⊂ TreeSize T' := by
  classical
  rw [Set.ssubset_def]
  refine ⟨fun _ hL => hL.mono hTT', fun hsub => ?_⟩
  obtain ⟨F, hF⟩ : ∃ F : (n : ℕ) → (Fin (ℓ n) → Bool) → Bool,
      ∀ C : Circuit (ℓ n₀), C.size ≤ T n₀ → ∃ x, C.eval x ≠ F n₀ x := by
    refine ⟨fun n => if h : (ℓ n + 4) * T n < 2 ^ ℓ n then
      Classical.choose (exists_not_eval_of_lt h) else fun _ => false, ?_⟩
    simpa only [dif_pos hlow] using Classical.choose_spec (exists_not_eval_of_lt hlow)
  exact padLanguage_not_inTreeSize hle F hF (hsub (padLanguage_inTreeSize hle F hup))

/-- Any `T` that the counting bound beats at a single length `n₀` is beaten by a larger
bound: take `ℓ n = min n n₀`. -/
theorem treeSize_ssubset_of_lt {T : ℕ → ℕ} {n₀ : ℕ} (h : (n₀ + 4) * T n₀ < 2 ^ n₀) :
    TreeSize T ⊂ TreeSize fun n => max (T n) (2 ^ min n n₀ * (min n n₀ + 1) + 1) :=
  treeSize_ssubset (ℓ := fun n => min n n₀) n₀ (fun n => Nat.min_le_left n n₀)
    (fun n => Nat.le_max_left _ _) (fun n => Nat.le_max_right _ _)
    (by simpa using h)

/-- A concrete instance, with `ℓ = 3`, the least length at which the local tree counting
bound (`exists_hard_function`) has content. -/
theorem treeSize_one_ssubset :
    TreeSize (fun _ => 1) ⊂ TreeSize fun n => max 1 (2 ^ min n 3 * (min n 3 + 1) + 1) :=
  treeSize_ssubset_of_lt (T := fun _ => 1) (n₀ := 3) (by norm_num)

/-- The smaller class of `treeSize_one_ssubset` is inhabited, so that inclusion is a strict
one between two nonempty classes. -/
theorem zero_mem_treeSize_one : (0 : Language Bool) ∈ TreeSize fun _ => 1 :=
  Language.zero_inTreeSize fun _ => le_refl 1

end BoolCircuit

## ===== TCSlib/Complexity/CircuitComplexity/NCAC.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Computability.Language
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.CircuitComplexity.Basic

/-!
# The circuit classes `NC` and `AC`

## Main definitions

* `BoolCircuit.TreeCircuitFamily` — one `BoolCircuit.Circuit n` per input length,
  with `language`, `IsPolySize`, `HasFaninTwo` and `HasPolylogDepth`.
* `Language.InNC` — [AB09, Def 6.24], `NC^d`; `BoolCircuit.NC` — `⋃_{i ≥ 1} NC^i`.
* `Language.InAC` — [AB09, Def 6.25], `AC^d`; `BoolCircuit.AC` — `⋃_{i ≥ 0} AC^i`.
* `BoolCircuit.Circuit.toBinary` — rebuilds every unbounded gate as a balanced
  binary tree of gates of the same type.

## Main results

* `Language.InNC.inAC` and `Language.InAC.inNC_succ` — `NC^i ⊆ AC^i ⊆ NC^{i+1}`
  [AB09, p. 118], hence `BoolCircuit.NC_eq_AC`.
* `BoolCircuit.toBinary_eval`, `toBinary_maxFanin_le`, `toBinary_depth_le`,
  `toBinary_size_le` — the four facts that inclusion needs.

[AB09, Ex 6.26], `PARITY ∈ NC¹`, is in `TCSlib.Complexity.CircuitComplexity.Parity`.
The size, depth and fan-in arithmetic these proofs run on is in
`TCSlib.Complexity.CircuitComplexity.Basic`.

## Divergences from Arora–Barak §6.7.1

* **What is formalized.** `Language.InNC d` and `Language.InAC d` are AB's `NC^d` and
  `AC^d` taken over `BoolCircuit.Circuit`, which is a *tree*: every gate feeds exactly
  one parent.  They are therefore AB's classes with fan-out restricted to `1` (formulas),
  where Def 6.1's circuits are DAGs.  AB's DAG classes are not defined anywhere in this
  development, and **no comparison between them and these is formalized**.  The next
  bullet describes the gap to AB; it is not a theorem of anything below.
* **Informal expectation, not proved here.** Unfolding a fan-in-`f` DAG of depth `d` into
  a tree duplicates a node once per consumer, blowing the node count up by a factor of at
  most `f ^ d`, so the fan-out-1 restriction is expected to be harmless exactly where a
  polynomial-size family stays polynomial: on the `NC` side at `i = 1` (`f = 2`,
  `d = O(log n)`), and on the `AC` side at `i = 0` (`f = poly(n)`, `d = O(1)`).  The two
  indices differ, so the `NC` boundary must not be carried across to `AC`.  Neither AB's
  DAG classes nor this unfolding is formalized, so
  **neither expectation is a theorem of this development**;
  `Circuit.size_succ_le_two_pow` (`Basic.lean`) proves only the tree-side bound.
* **Size measure.** `IsPolySize` is AB's "poly(n) size", measured by `Circuit.size`, which
  diverges from Def 6.1 in both directions.  It *lowers* the count by charging `1` for a
  `k`-ary gate where AB charges `k − 1` vertices — unbounded here, not a constant, since
  `AC^i` is the unbounded-fan-in class — and by not counting AB's `n` input vertices.  It
  *raises* the count by charging every literal occurrence a separate leaf, since a tree
  has no shared input vertices and no gate reuse.
* **Fan-in.** Bounded fan-in is the predicate `Circuit.maxFanin ≤ 2` over the one
  unbounded-fan-in `Circuit` type, not a separate inductive type — this is the idiom the
  LMN development already uses (`maxFanin ≤ w` as a hypothesis), and it lets
  `toBinary : Circuit n → Circuit n` be a plain function whose four properties are
  ordinary lemmas about one type.  `BoolCircuit.FeedForward`, the layered DAG `PPoly.lean` uses,
  was rejected because `toBinary` recurses over a gate's child list, which it has not.
* **Basis.** `Circuit` negates only at literals, so a `NOT` gate is free and contributes
  no depth, where AB's Def 6.1 basis `{∧, ∨, ¬}` charges one for it.
* **`O(log^d n)`.** Written `∃ b, ∀ n, depth ≤ b * (Nat.log 2 n + 1) ^ d`, the shape
  `PPoly.lean` uses for size.  The `+ 1` repairs the same degeneracy: `Nat.log 2 n = 0`
  for `n ≤ 1`, so `b * (Nat.log 2 n) ^ d` would force depth `0` at those lengths.
* **`NC ⊆ P/poly`.** Statable — `BoolCircuit.NC` and `BoolCircuit.PPoly` are both
  `Set (Language Bool)` — but not provable here: there is no bridge from
  `BoolCircuit.Circuit` to `BoolCircuit.CircuitFamily` (`backlog.md` §3, deferred follow-ups).
* **Uniformity.** AB's "one can also define uniform `NC`" needs logspace and is out of
  scope for now (no logspace machinery).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-! ### Circuit families -/

/-- A non-uniform family of Boolean circuits, one per input length. -/
structure TreeCircuitFamily where
  /-- The circuit handling inputs of length `n`. -/
  circuit : (n : ℕ) → Circuit n

namespace TreeCircuitFamily

variable (C : TreeCircuitFamily)

/-- The family accepts `w` when the circuit for length `w.length` outputs `true`. -/
def Accepts (w : List Bool) : Prop :=
  (C.circuit w.length).eval w.get = true

/-- The language decided by the family. -/
def language : Language Bool :=
  {w | C.Accepts w}

/-- Membership in the decided language, unfolded to the circuit's output. -/
@[simp]
theorem mem_language_iff (w : List Bool) :
    w ∈ C.language ↔ (C.circuit w.length).eval w.get = true :=
  Iff.rfl

/-- The family has polynomial size. -/
def IsPolySize : Prop :=
  ∃ a k : ℕ, ∀ n, (C.circuit n).size ≤ a * (n + 1) ^ k

/-- Every gate of every circuit in the family has at most two inputs. -/
def HasFaninTwo : Prop :=
  ∀ n, (C.circuit n).maxFanin ≤ 2

/-- The family has polylogarithmic depth `O(log^d n)` (constant depth when `d = 0`). -/
def HasPolylogDepth (d : ℕ) : Prop :=
  ∃ b : ℕ, ∀ n, (C.circuit n).depth ≤ b * (Nat.log 2 n + 1) ^ d

end TreeCircuitFamily

end BoolCircuit

/-- `L ∈ NC^d`: a polynomial-size fan-in-2 family of depth `O(log^d n)` decides `L`.
[AB09, Def 6.24] -/
def Language.InNC (d : ℕ) (L : Language Bool) : Prop :=
  ∃ C : BoolCircuit.TreeCircuitFamily,
    C.HasFaninTwo ∧ C.IsPolySize ∧ C.HasPolylogDepth d ∧ C.language = L

/-- `L ∈ AC^d`: as `NC^d`, but gates may have unbounded fan-in.  [AB09, Def 6.25] -/
def Language.InAC (d : ℕ) (L : Language Bool) : Prop :=
  ∃ C : BoolCircuit.TreeCircuitFamily,
    C.IsPolySize ∧ C.HasPolylogDepth d ∧ C.language = L

namespace BoolCircuit

/-- `NC^d` as a set of languages. -/
def NCLevel (d : ℕ) : Set (Language Bool) := {L | L.InNC d}

/-- `AC^d` as a set of languages. -/
def ACLevel (d : ℕ) : Set (Language Bool) := {L | L.InAC d}

/-- `NC = ⋃_{i ≥ 1} NC^i`.  [AB09, Def 6.24] -/
def NC : Set (Language Bool) := ⋃ i ∈ Set.Ici 1, NCLevel i

/-- `AC = ⋃_{i ≥ 0} AC^i`.  [AB09, Def 6.25] -/
def AC : Set (Language Bool) := ⋃ i, ACLevel i

/-- Membership in `NC` is membership in some `NC^i` with `i ≥ 1`. -/
theorem mem_NC_iff (L : Language Bool) : L ∈ NC ↔ ∃ i, 1 ≤ i ∧ L.InNC i := by
  simp [NC, NCLevel, Set.mem_iUnion]

/-- Membership in `AC` is membership in some `AC^i`. -/
theorem mem_AC_iff (L : Language Bool) : L ∈ AC ↔ ∃ i, L.InAC i := by
  simp [AC, ACLevel, Set.mem_iUnion]

end BoolCircuit

/-- `NC^i ⊆ AC^i`: forget the fan-in bound.  [AB09, p. 118] -/
theorem Language.InNC.inAC {d : ℕ} {L : Language Bool} (h : L.InNC d) : L.InAC d := by
  obtain ⟨C, _, hs, hd, hl⟩ := h
  exact ⟨C, hs, hd, hl⟩

namespace BoolCircuit

variable {n : ℕ}

/-! ### Simulating an unbounded gate by a balanced binary tree -/

/-- Pair adjacent children under a gate of type `b`, halving the list. -/
private def pairUp (b : Bool) : List (Circuit n) → List (Circuit n)
  | [] => []
  | [c] => [c]
  | c₁ :: c₂ :: cs => Circuit.node b [c₁, c₂] :: pairUp b cs

/-- Pairing halves the list, rounding up. -/
private theorem length_pairUp (b : Bool) :
    ∀ cs : List (Circuit n), (pairUp b cs).length = (cs.length + 1) / 2
  | [] => by simp [pairUp]
  | [_] => by simp [pairUp]
  | _ :: _ :: cs => by
      have := length_pairUp b cs
      simp only [pairUp, List.length_cons] at *
      omega

/-- Pairing preserves the value of the surrounding gate. -/
private theorem eval_node_pairUp (b : Bool) (x : Fin n → Bool) :
    ∀ cs : List (Circuit n),
      (Circuit.node b (pairUp b cs)).eval x = (Circuit.node b cs).eval x
  | [] => rfl
  | [_] => by cases b <;> simp [pairUp, Circuit.eval]
  | c₁ :: c₂ :: cs => by
      have := eval_node_pairUp b x cs
      cases b <;>
        simp only [pairUp, Circuit.eval, List.foldr_cons, List.foldr_nil] at * <;>
        simp [this, Bool.and_assoc, Bool.or_assoc]

/-- Pairing adds at most one to the depth. -/
private theorem maxDepth_pairUp (b : Bool) :
    ∀ cs : List (Circuit n), Circuit.maxDepth (pairUp b cs) ≤ 1 + Circuit.maxDepth cs
  | [] => by simp [pairUp, Circuit.maxDepth_nil]
  | [c] => by simp [pairUp]
  | c₁ :: c₂ :: cs => by
      have ih := maxDepth_pairUp b cs
      have h1 : (Circuit.node b [c₁, c₂]).depth
          = 1 + max c₁.depth (max c₂.depth 0) := by
        rw [Circuit.depth_node, Circuit.maxDepth_cons, Circuit.maxDepth_cons, Circuit.maxDepth_nil]
      simp only [pairUp, Circuit.maxDepth_cons, h1]
      omega

/-- Pairing does not increase the total size plus length. -/
private theorem sumSize_pairUp (b : Bool) :
    ∀ cs : List (Circuit n),
      Circuit.sumSize (pairUp b cs) + (pairUp b cs).length ≤
        Circuit.sumSize cs + cs.length
  | [] => le_refl 0
  | [_] => le_refl _
  | c₁ :: c₂ :: cs => by
      have ih := sumSize_pairUp b cs
      have h1 : (Circuit.node b [c₁, c₂]).size = 1 + (c₁.size + (c₂.size + 0)) := by
        rw [Circuit.size_node, Circuit.sumSize_cons, Circuit.sumSize_cons, Circuit.sumSize_nil]
      simp only [pairUp, Circuit.sumSize_cons, h1, List.length_cons]
      omega

/-- Pairing introduces only fan-in-2 gates. -/
private theorem maxFaninL_pairUp (b : Bool) :
    ∀ cs : List (Circuit n), Circuit.maxFaninL (pairUp b cs) ≤ max 2 (Circuit.maxFaninL cs)
  | [] => Nat.zero_le _
  | [c] => by simp [pairUp, Circuit.maxFaninL_cons, Circuit.maxFaninL_nil]
  | c₁ :: c₂ :: cs => by
      have ih := maxFaninL_pairUp b cs
      have h1 : (Circuit.node b [c₁, c₂]).maxFanin
          = max 2 (max c₁.maxFanin (max c₂.maxFanin 0)) := by
        rw [Circuit.maxFanin_node, Circuit.maxFaninL_cons, Circuit.maxFaninL_cons,
          Circuit.maxFaninL_nil]
        norm_num
      simp only [pairUp, Circuit.maxFaninL_cons, h1]
      omega

/-- Repeatedly pair a child list, `k` rounds at most, into a single circuit. -/
private def combineFuel (b : Bool) : ℕ → List (Circuit n) → Circuit n
  | 0, cs => Circuit.node b cs
  | _ + 1, [] => Circuit.node b []
  | _ + 1, [c] => c
  | k + 1, c₁ :: c₂ :: cs => combineFuel b k (pairUp b (c₁ :: c₂ :: cs))

/-- Combine a child list into a balanced binary tree of gates of type `b`. -/
private def combine (b : Bool) (cs : List (Circuit n)) : Circuit n :=
  combineFuel b cs.length cs

/-- Combining computes the same value as the unbounded gate. -/
private theorem combineFuel_eval (b : Bool) (x : Fin n → Bool) :
    ∀ (k : ℕ) (cs : List (Circuit n)),
      (combineFuel b k cs).eval x = (Circuit.node b cs).eval x
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | _ + 1, [c] => by cases b <;> simp [combineFuel, Circuit.eval]
  | k + 1, c₁ :: c₂ :: cs => by
      show (combineFuel b k (pairUp b (c₁ :: c₂ :: cs))).eval x = _
      rw [combineFuel_eval b x k, eval_node_pairUp]

/-- Combining produces only fan-in-2 gates, given enough rounds. -/
private theorem combineFuel_maxFanin (b : Bool) :
    ∀ (k : ℕ) (cs : List (Circuit n)), cs.length ≤ k →
      (combineFuel b k cs).maxFanin ≤ max 2 (Circuit.maxFaninL cs)
  | 0, [], _ => by simp [combineFuel, Circuit.maxFanin_node, Circuit.maxFaninL_nil]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [combineFuel, Circuit.maxFanin_node, Circuit.maxFaninL_nil]
  | _ + 1, [c], _ => by
      show c.maxFanin ≤ _
      rw [Circuit.maxFaninL_cons, Circuit.maxFaninL_nil]
      omega
  | k + 1, c₁ :: c₂ :: cs, h => by
      have hp := length_pairUp b (c₁ :: c₂ :: cs)
      have hlen : (pairUp b (c₁ :: c₂ :: cs)).length ≤ k := by
        simp only [List.length_cons] at h hp ⊢; omega
      have ih := combineFuel_maxFanin b k _ hlen
      have h2 := maxFaninL_pairUp b (c₁ :: c₂ :: cs)
      show (combineFuel b k (pairUp b (c₁ :: c₂ :: cs))).maxFanin ≤ _
      omega

/-- Combining `m` children costs `⌈log₂ m⌉` extra levels of depth. -/
private theorem combineFuel_depth (b : Bool) :
    ∀ (k : ℕ) (cs : List (Circuit n)), cs.length ≤ k →
      (combineFuel b k cs).depth ≤ Circuit.maxDepth cs + Nat.clog 2 cs.length + 1
  | 0, [], _ => by simp [combineFuel, Circuit.depth_node, Circuit.maxDepth_nil]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [combineFuel, Circuit.depth_node, Circuit.maxDepth_nil]
  | _ + 1, [c], _ => by
      show c.depth ≤ _
      rw [Circuit.maxDepth_cons, Circuit.maxDepth_nil]
      simp
  | k + 1, c₁ :: c₂ :: cs, h => by
      have hp := length_pairUp b (c₁ :: c₂ :: cs)
      have hlen : (pairUp b (c₁ :: c₂ :: cs)).length ≤ k := by
        simp only [List.length_cons] at h hp ⊢; omega
      have ih := combineFuel_depth b k _ hlen
      have h2 := maxDepth_pairUp b (c₁ :: c₂ :: cs)
      have hclog : Nat.clog 2 (c₁ :: c₂ :: cs).length
          = Nat.clog 2 ((pairUp b (c₁ :: c₂ :: cs)).length) + 1 := by
        rw [hp]
        have := Nat.clog_of_two_le (b := 2) (n := (c₁ :: c₂ :: cs).length)
          (by norm_num) (by simp)
        simpa using this
      show (combineFuel b k (pairUp b (c₁ :: c₂ :: cs))).depth ≤ _
      omega

/-- Combining `m` children costs at most `m` extra gates. -/
private theorem combineFuel_size (b : Bool) :
    ∀ (k : ℕ) (cs : List (Circuit n)),
      (combineFuel b k cs).size ≤ Circuit.sumSize cs + cs.length + 1
  | 0, cs => by show (Circuit.node b cs).size ≤ _; rw [Circuit.size_node]; omega
  | _ + 1, [] => by simp [combineFuel, Circuit.size_node, Circuit.sumSize_nil]
  | _ + 1, [c] => by show c.size ≤ _; rw [Circuit.sumSize_cons, Circuit.sumSize_nil]; omega
  | k + 1, c₁ :: c₂ :: cs => by
      have ih := combineFuel_size b k (pairUp b (c₁ :: c₂ :: cs))
      have h2 := sumSize_pairUp b (c₁ :: c₂ :: cs)
      show (combineFuel b k (pairUp b (c₁ :: c₂ :: cs))).size ≤ _
      omega

/-- `combine` computes the unbounded gate. -/
private theorem combine_eval (b : Bool) (cs : List (Circuit n)) (x : Fin n → Bool) :
    (combine b cs).eval x = (Circuit.node b cs).eval x :=
  combineFuel_eval b x _ cs

/-- `combine` has fan-in 2, unless a child already had more. -/
private theorem combine_maxFanin (b : Bool) (cs : List (Circuit n)) :
    (combine b cs).maxFanin ≤ max 2 (Circuit.maxFaninL cs) :=
  combineFuel_maxFanin b _ cs (le_refl _)

/-- `combine` adds `⌈log₂ |cs|⌉ + 1` to the children's depth. -/
private theorem combine_depth (b : Bool) (cs : List (Circuit n)) :
    (combine b cs).depth ≤ Circuit.maxDepth cs + Nat.clog 2 cs.length + 1 :=
  combineFuel_depth b _ cs (le_refl _)

/-- `combine` adds `|cs| + 1` to the children's total size. -/
private theorem combine_size (b : Bool) (cs : List (Circuit n)) :
    (combine b cs).size ≤ Circuit.sumSize cs + cs.length + 1 :=
  combineFuel_size b _ cs

/-- Rebuild every gate of a circuit as a balanced binary tree of gates of the same
type, so that the result has fan-in `2`.  [AB09, p. 118] -/
def Circuit.toBinary : Circuit n → Circuit n
  | .lit l => .lit l
  | .node b cs => combine b (cs.map Circuit.toBinary)

/-- A gate's value is unchanged when its children are replaced by equivalent ones. -/
private theorem eval_node_map (b : Bool) (x : Fin n → Bool) (f : Circuit n → Circuit n) :
    ∀ cs : List (Circuit n), (∀ c ∈ cs, (f c).eval x = c.eval x) →
      (Circuit.node b (cs.map f)).eval x = (Circuit.node b cs).eval x
  | [], _ => rfl
  | c :: cs, h => by
      have ih := eval_node_map b x f cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hc := h c (List.mem_cons_self ..)
      cases b <;>
        simp only [List.map_cons, Circuit.eval, List.foldr_cons] at ih ⊢ <;>
        rw [hc, ih]

/-- A depth bound on every image element bounds the image's depth. -/
private theorem maxDepth_map_le (f : Circuit n → Circuit n) (m : ℕ) :
    ∀ cs : List (Circuit n), (∀ c ∈ cs, (f c).depth ≤ m) →
      Circuit.maxDepth (cs.map f) ≤ m
  | [], _ => Nat.zero_le _
  | c :: cs, h => by
      have ih := maxDepth_map_le f m cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hc := h c (List.mem_cons_self ..)
      simp only [List.map_cons, Circuit.maxDepth_cons]
      omega

/-- A fan-in bound on every image element bounds the image's fan-in. -/
private theorem maxFaninL_map_le (f : Circuit n → Circuit n) (m : ℕ) :
    ∀ cs : List (Circuit n), (∀ c ∈ cs, (f c).maxFanin ≤ m) →
      Circuit.maxFaninL (cs.map f) ≤ m
  | [], _ => Nat.zero_le _
  | c :: cs, h => by
      have ih := maxFaninL_map_le f m cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hc := h c (List.mem_cons_self ..)
      simp only [List.map_cons, Circuit.maxFaninL_cons]
      omega

/-- `toBinary` computes the same function. -/
theorem toBinary_eval : ∀ (c : Circuit n) (x : Fin n → Bool), c.toBinary.eval x = c.eval x := by
  intro c
  induction c using Circuit.ind with
  | hlit l => intro x; simp only [Circuit.toBinary]
  | hnode b cs ih =>
      intro x
      simp only [Circuit.toBinary]
      rw [combine_eval]
      exact eval_node_map b x Circuit.toBinary cs (fun c hc => ih c hc x)

/-- `toBinary` produces a fan-in-2 circuit. -/
theorem toBinary_maxFanin_le : ∀ c : Circuit n, c.toBinary.maxFanin ≤ 2 := by
  intro c
  induction c using Circuit.ind with
  | hlit l => simp [Circuit.toBinary, Circuit.maxFanin]
  | hnode b cs ih =>
      simp only [Circuit.toBinary]
      have h1 := combine_maxFanin b (cs.map Circuit.toBinary)
      have h2 := maxFaninL_map_le Circuit.toBinary 2 cs ih
      omega

/-- The list form of `toBinary_size_le`, in the strengthened form the induction needs. -/
private theorem sumSize_map_toBinary :
    ∀ cs : List (Circuit n), (∀ c ∈ cs, c.toBinary.size + 1 ≤ 3 * c.size) →
      Circuit.sumSize (cs.map Circuit.toBinary) + cs.length ≤ 3 * Circuit.sumSize cs
  | [], _ => by simp [Circuit.sumSize_nil]
  | c :: cs, h => by
      have ih := sumSize_map_toBinary cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hc := h c (List.mem_cons_self ..)
      simp only [List.map_cons, Circuit.sumSize_cons, List.length_cons]
      omega

/-- `toBinary` at most triples the size, with one unit to spare. -/
private theorem toBinary_size_succ_le : ∀ c : Circuit n, c.toBinary.size + 1 ≤ 3 * c.size := by
  intro c
  induction c using Circuit.ind with
  | hlit l => simp [Circuit.toBinary, Circuit.size]
  | hnode b cs ih =>
      simp only [Circuit.toBinary]
      have h1 := combine_size b (cs.map Circuit.toBinary)
      have h2 := sumSize_map_toBinary cs ih
      rw [Circuit.size_node]
      simp only [List.length_map] at h1
      omega

/-- `toBinary` at most triples the size. -/
theorem toBinary_size_le (c : Circuit n) : c.toBinary.size ≤ 3 * c.size :=
  le_trans (Nat.le_succ _) (toBinary_size_succ_le c)

/-- `toBinary` multiplies the depth by `⌈log₂ w⌉ + 1`, where `w` bounds the fan-in. -/
theorem toBinary_depth_le {w : ℕ} : ∀ c : Circuit n, c.maxFanin ≤ w →
    c.toBinary.depth ≤ c.depth * (Nat.clog 2 w + 1) := by
  intro c
  induction c using Circuit.ind with
  | hlit l => intro _; simp [Circuit.toBinary, Circuit.depth]
  | hnode b cs ih =>
      intro h
      rw [Circuit.maxFanin_node] at h
      have hlen : cs.length ≤ w := le_trans (le_max_left _ _) h
      have hfan : Circuit.maxFaninL cs ≤ w := le_trans (le_max_right _ _) h
      have hB : Circuit.maxDepth (cs.map Circuit.toBinary)
          ≤ Circuit.maxDepth cs * (Nat.clog 2 w + 1) :=
        maxDepth_map_le _ _ cs fun c hc =>
          le_trans (ih c hc (le_trans (Circuit.maxFanin_le_maxFaninL hc) hfan))
            (Nat.mul_le_mul_right _ (Circuit.depth_le_maxDepth hc))
      have hC : Nat.clog 2 cs.length ≤ Nat.clog 2 w := Nat.clog_mono_right 2 hlen
      simp only [Circuit.toBinary]
      refine le_trans (combine_depth b (cs.map Circuit.toBinary)) ?_
      rw [Circuit.depth_node, Nat.add_mul, Nat.one_mul, List.length_map]
      omega

/-- `⌈log₂⌉` of a polynomial is `O(log n)`. -/
private theorem clog_poly_le (a k m : ℕ) :
    Nat.clog 2 (a * (m + 1) ^ k) ≤ a + k * (Nat.log 2 m + 1) := by
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  calc a * (m + 1) ^ k
      ≤ 2 ^ a * (2 ^ (Nat.log 2 m + 1)) ^ k :=
        Nat.mul_le_mul (Nat.le_of_lt a.lt_two_pow_self)
          (Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self (by norm_num) m) k)
    _ = 2 ^ (a + k * (Nat.log 2 m + 1)) := by
        rw [← pow_mul, ← pow_add, Nat.mul_comm (Nat.log 2 m + 1) k]

end BoolCircuit

/-- `AC^i ⊆ NC^{i+1}`: rebuild every unbounded gate as a tree of fan-in-2 gates, which
costs a factor `O(log n)` in depth because the fan-in is at most the size, hence
`poly(n)`.  [AB09, p. 118]

**Proof sketch.** Let `{Cₙ}` decide `L` with `|Cₙ| ≤ a(n+1)ᵏ` and `depth Cₙ ≤ b(log n+1)ⁱ`.
A gate's fan-in never exceeds the circuit's size, so every gate of `Cₙ` has at most
`w = a(n+1)ᵏ` children, and `⌈log₂ w⌉ + 1 ≤ (a+k+1)(log n + 1)`.  Replacing each gate by
`Circuit.toBinary`'s balanced binary tree of gates of the same type multiplies the depth by
`⌈log₂ w⌉ + 1`, so the new depth is at most `b(a+k+1)(log n+1)^{i+1}`; it at most triples
the size, so the family is still polynomial; it has fan-in `2`; and it computes the same
function, so it decides the same language. -/
theorem Language.InAC.inNC_succ {d : ℕ} {L : Language Bool} (h : L.InAC d) :
    L.InNC (d + 1) := by
  classical
  obtain ⟨C, ⟨a, k, hsize⟩, ⟨b, hdepth⟩, hlang⟩ := h
  refine ⟨⟨fun n => (C.circuit n).toBinary⟩, fun n => BoolCircuit.toBinary_maxFanin_le _,
    ⟨3 * a, k, fun n => ?_⟩, ⟨b * (a + k + 1), fun n => ?_⟩, ?_⟩
  · calc ((C.circuit n).toBinary).size
        ≤ 3 * (C.circuit n).size := BoolCircuit.toBinary_size_le _
      _ ≤ 3 * (a * (n + 1) ^ k) := Nat.mul_le_mul_left 3 (hsize n)
      _ = 3 * a * (n + 1) ^ k := (Nat.mul_assoc 3 a _).symm
  · have hfan : (C.circuit n).maxFanin ≤ a * (n + 1) ^ k :=
      le_trans (BoolCircuit.Circuit.maxFanin_le_size _) (hsize n)
    have hK : Nat.clog 2 (a * (n + 1) ^ k) + 1 ≤ (a + k + 1) * (Nat.log 2 n + 1) := by
      have hpoly := BoolCircuit.clog_poly_le a k n
      have e1 : a ≤ a * (Nat.log 2 n + 1) := Nat.le_mul_of_pos_right a (by omega)
      have e2 : (a + k + 1) * (Nat.log 2 n + 1)
          = a * (Nat.log 2 n + 1) + k * (Nat.log 2 n + 1) + (Nat.log 2 n + 1) := by ring
      omega
    calc ((C.circuit n).toBinary).depth
        ≤ (C.circuit n).depth * (Nat.clog 2 (a * (n + 1) ^ k) + 1) :=
          BoolCircuit.toBinary_depth_le _ hfan
      _ ≤ (b * (Nat.log 2 n + 1) ^ d) * ((a + k + 1) * (Nat.log 2 n + 1)) :=
          Nat.mul_le_mul (hdepth n) hK
      _ = b * (a + k + 1) * (Nat.log 2 n + 1) ^ (d + 1) := by ring
  · rw [← hlang]
    ext w
    simp [BoolCircuit.TreeCircuitFamily.mem_language_iff, BoolCircuit.toBinary_eval]

namespace BoolCircuit

/-- `NC^i ⊆ AC^i`.  [AB09, p. 118] -/
theorem NCLevel_subset_ACLevel (i : ℕ) : NCLevel i ⊆ ACLevel i :=
  fun _ h => Language.InNC.inAC h

/-- `AC^i ⊆ NC^{i+1}`.  [AB09, p. 118] -/
theorem ACLevel_subset_NCLevel_succ (i : ℕ) : ACLevel i ⊆ NCLevel (i + 1) :=
  fun _ h => Language.InAC.inNC_succ h

/-- The two inclusions make the **unions** coincide: `NC = AC` — no levelwise
equality is asserted — a corollary of [AB09, p. 118], which states the
inclusions only. -/
theorem NC_eq_AC : NC = AC := by
  ext L
  rw [mem_NC_iff, mem_AC_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, hi.inAC⟩
  · rintro ⟨i, hi⟩
    exact ⟨i + 1, Nat.le_add_left 1 i, hi.inNC_succ⟩

end BoolCircuit

## ===== TCSlib/Complexity/CircuitComplexity/PPoly.lean =====

/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.CircuitComplexity.FeedForward

/-!
# P/poly

The class of languages decided by polynomial-size non-uniform Boolean circuit
families, built on `BoolCircuit.FeedForward` (the model used by the Razborov–Smolensky
development) and shaped after Mathlib's `Language.IsRegular`: a complexity class
is a predicate on languages.

## Main definitions

* `BoolCircuit.CircuitFamily` — one single-output circuit per input length, all layers finite.
* `Language.InSIZE` — [AB09, Def 6.2].
* `Language.InPPoly` — [AB09, Def 6.5], `P/poly = ⋃_c SIZE(n^c)`.
* `BoolCircuit.PPoly` — the same class as a `Set (Language Bool)`.

## Main results

* `Language.inPPoly_iff` — `P/poly` membership repackaged as one family that
  carries its own size bound.

## Alphabet

Languages are over `Bool`, matching `Turing.FinEncoding`'s binary encodings and
cslib's `MultiTapeTM k Bool State`, so that a future `P ⊆ P/poly` is statable
without transport.  Circuits stay on `Fin 2` internally (the Razborov–Smolensky
gate sets are `GateOp (Fin 2)`); `finTwoEquiv` converts at the boundary.

## Divergences from Arora–Barak §6.1

All preserve the polynomial union `P/poly`; **none is claimed to preserve a
fixed class `SIZE(T)`**, and in general none does: `Language.allOnes` lies in
this file's `InSIZE (fun _ => 1)` (`SizeClasses.lean`), while [AB09, Def 6.1]
counts the `n` input vertices, so no size-`1` circuit exists there for `n ≥ 2`.
`Language.InSIZE` is the finite, layered, unbounded-fan-in, non-input-counting
size class of *this* model; quantitative transfer to AB's `SIZE(T)` needs an
explicit simulation with a transformed budget. AB Def 6.1 fixes fan-in 2; we use unbounded `stdGateOps`,
which AB calls "essentially without loss of generality" (fan-in `f` costs `f - 1`
gates) and which is AB's own convention for `AC` (Def 6.25) — fan-in matters only
under a depth restriction, and `P/poly` imposes none. AB's basis is `{∧, ∨, ¬}`;
ours adds `id` (needed for layer padding) and recovers `∨` by De Morgan. AB counts
input vertices in `|C|` and allows arbitrary DAGs; we count non-input nodes and
require layering, costing `+n` and a factor `≤ s` respectively. AB writes
`∃ c, ∀ n, |C n| ≤ n ^ c`; we write `∃ a k, ∀ n, size ≤ a * (n + 1) ^ k`, which
repairs a degeneracy in AB's literal form (`n ^ c` forces `|C 0| ≤ 0`).
Further graph conventions, collected: a singleton output type does not forbid
unused nodes on earlier layers; inputs may go unread; `Gate.inputs` need not be
injective, so repeated wires are allowed — all harmless for computational
power, with size/depth accounting model-specific.  `stdGateOps` contains
`andGateOp 0`, the empty product, i.e. a **constant-one** operation; there is
no primitive constant-false (`NOT` of the empty `AND` provides it).

## Trap

`FeedForward.size` is `Nat.card`-based, so it returns `0` on an infinite type:
without `CircuitFamily.finite`, `IsPolySize` would hold vacuously and `P/poly`
would be every language.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

open FeedForward

/-- A non-uniform family of single-output Boolean circuits, one per input length. -/
structure CircuitFamily where
  /-- The circuit handling inputs of length `n`. -/
  circuit : (n : ℕ) → FeedForward (Fin 2) (Fin n) Unit
  /-- Every layer of every circuit in the family is finite. -/
  finite : ∀ n, (circuit n).Finite

namespace CircuitFamily

variable (C : CircuitFamily)

/-- The family accepts `w` when the circuit for length `w.length` outputs `1`.
Words are `List Bool`; `finTwoEquiv` converts at the circuit boundary. -/
def Accepts (w : List Bool) : Prop :=
  (C.circuit w.length).eval₁ (fun i => finTwoEquiv.symm (w.get i)) = 1

/-- The language decided by the family. -/
def language : Language Bool :=
  {w | C.Accepts w}

/-- Membership in the decided language, unfolded to the circuit's output. -/
@[simp]
theorem mem_language_iff (w : List Bool) :
    w ∈ C.language ↔
      (C.circuit w.length).eval₁ (fun i => finTwoEquiv.symm (w.get i)) = 1 :=
  Iff.rfl

/-- Every circuit in the family draws its gates from `S`. -/
def OnlyUsesGates (S : Set (GateOp (Fin 2))) : Prop :=
  ∀ n, (C.circuit n).onlyUsesGates S

/-- The family has polynomial size. -/
def IsPolySize : Prop :=
  ∃ a k : ℕ, ∀ n, (C.circuit n).size ≤ a * (n + 1) ^ k

end CircuitFamily

end BoolCircuit

/-- `L ∈ SIZE(T)`: some `stdGateOps` family decides `L` with the length-`n`
circuit of size at most `T n`.  [AB09, Def 6.2] -/
def Language.InSIZE (T : ℕ → ℕ) (L : Language Bool) : Prop :=
  ∃ C : BoolCircuit.CircuitFamily,
    C.OnlyUsesGates BoolCircuit.stdGateOps ∧ (∀ n, (C.circuit n).size ≤ T n) ∧ C.language = L

/-- A language is in `P/poly` when some polynomial-size circuit family decides
it.  [AB09, Def 6.5] -/
def Language.InPPoly (L : Language Bool) : Prop :=
  ∃ a k : ℕ, L.InSIZE (fun n => a * (n + 1) ^ k)

/-- `P/poly` membership as one family carrying its own size bound. -/
theorem Language.inPPoly_iff (L : Language Bool) :
    L.InPPoly ↔ ∃ C : BoolCircuit.CircuitFamily,
      C.OnlyUsesGates BoolCircuit.stdGateOps ∧ C.IsPolySize ∧ C.language = L := by
  constructor
  · rintro ⟨a, k, C, hG, hS, hL⟩
    exact ⟨C, hG, ⟨a, k, hS⟩, hL⟩
  · rintro ⟨C, hG, ⟨a, k, hS⟩, hL⟩
    exact ⟨a, k, C, hG, hS, hL⟩

namespace BoolCircuit

/-- `P/poly` packaged as a set of languages, for `L ∈ PPoly` notation. -/
def PPoly : Set (Language Bool) :=
  {L | L.InPPoly}

/-- Set membership in `PPoly` agrees with the predicate `Language.InPPoly`. -/
@[simp]
theorem mem_PPoly_iff (L : Language Bool) : L ∈ PPoly ↔ L.InPPoly :=
  Iff.rfl

end BoolCircuit

## ===== TCSlib/Complexity/CircuitComplexity/Parity.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.CircuitComplexity.NCAC

/-!
# `PARITY` is in `NC¹`

## Main definitions

* `BoolCircuit.parityCircuit` — the balanced binary XOR tree on `n` input bits.
* `Language.parity` — [AB09, Ex 6.26]'s `PARITY = {x : x has an odd number of 1s}`.

## Main results

* `Language.parity_inNC_one` — [AB09, Ex 6.26], `PARITY ∈ NC¹`.
* `BoolCircuit.parityCircuit_eval`, `_maxFanin_le`, `_depth_le`, `_size_le` — the four
  facts that membership needs; `_eval_zero` and `_eval_one` pin the two input lengths at
  which `Nat.log 2 n = 0`.
* `Language.mem_parity_iff` — `PARITY` membership as the iterated XOR of the letters.

## Divergences from Arora–Barak Example 6.26

* **Dual pairs.** AB's tree has an XOR gate at every internal node.  `Circuit`'s gates are
  `AND` and `OR` and it negates only at literals, so each node here carries a *pair* — a
  circuit for the XOR of its leaves and a circuit for the complement — and `xorNode` builds
  a parent pair from its children's as `(a ∧ b') ∨ (a' ∧ b)` and `(a ∧ b) ∨ (a' ∧ b')`.
  That costs two levels per halving where AB's costs one, so the depth is at most `2⌈log₂ n⌉ + 2`
  against AB's exact `⌈log₂ n⌉` (at `n = 1` this circuit is a bare literal of
  depth `0`; the displayed expression is an upper bound, not the depth).  Both are `O(log n)`, which is all `NC¹` asks.
* **Constants.** `4 * (Nat.log 2 n + 1)` for depth and `32 * (n + 1) ^ 4` for size are what
  this construction gives.  AB states neither and neither is claimed optimal.  The size
  bound is not a separate recurrence: it is read off the depth bound and fan-in `2` through
  `Circuit.size_succ_le_two_pow`.
* **Fan-out 1, and the size measure.** Both are inherited from, and recorded in,
  `TCSlib.Complexity.CircuitComplexity.NCAC`.  `NC¹` here is that file's `Language.InNC 1`,
  which is AB's `NC¹` restricted to fan-out 1; no comparison with AB's DAG class is
  formalized there or here.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-- The XOR of two circuits, as a pair of a circuit and a circuit for its complement. -/
private def xorNode (p q : Circuit n × Circuit n) : Circuit n × Circuit n :=
  (Circuit.node false [Circuit.node true [p.1, q.2], Circuit.node true [p.2, q.1]],
   Circuit.node false [Circuit.node true [p.1, q.1], Circuit.node true [p.2, q.2]])

/-- A pair is dual when its second component computes the negation of its first. -/
private def IsDual (x : Fin n → Bool) (p : Circuit n × Circuit n) : Prop :=
  p.2.eval x = !p.1.eval x

/-- `xorNode` computes the XOR of the two first components. -/
private theorem xorNode_eval {x : Fin n → Bool} {p q : Circuit n × Circuit n}
    (hp : IsDual x p) (hq : IsDual x q) :
    (xorNode p q).1.eval x = Bool.xor (p.1.eval x) (q.1.eval x) := by
  simp only [xorNode, Circuit.eval, List.foldr_cons, List.foldr_nil]
  rw [show q.2.eval x = !q.1.eval x from hq, show p.2.eval x = !p.1.eval x from hp]
  cases p.1.eval x <;> cases q.1.eval x <;> simp

/-- `xorNode` again produces a dual pair. -/
private theorem xorNode_isDual {x : Fin n → Bool} {p q : Circuit n × Circuit n}
    (hp : IsDual x p) (hq : IsDual x q) : IsDual x (xorNode p q) := by
  simp only [IsDual, xorNode, Circuit.eval, List.foldr_cons, List.foldr_nil]
  rw [show q.2.eval x = !q.1.eval x from hq, show p.2.eval x = !p.1.eval x from hp]
  cases p.1.eval x <;> cases q.1.eval x <;> simp

/-- The XOR of the first components of a list of pairs. -/
private def xorAll (x : Fin n → Bool) (ps : List (Circuit n × Circuit n)) : Bool :=
  ps.foldr (fun p acc => Bool.xor (p.1.eval x) acc) false

/-- Maximum depth over both components of a list of pairs. -/
private def pairDepth (ps : List (Circuit n × Circuit n)) : ℕ :=
  ps.foldr (fun p acc => max (max p.1.depth p.2.depth) acc) 0

/-- Maximum fan-in over both components of a list of pairs. -/
private def pairFanin (ps : List (Circuit n × Circuit n)) : ℕ :=
  ps.foldr (fun p acc => max (max p.1.maxFanin p.2.maxFanin) acc) 0

/-- `xorAll` on a cons cell. -/
private theorem xorAll_cons (x : Fin n → Bool) (p : Circuit n × Circuit n)
    (ps : List (Circuit n × Circuit n)) :
    xorAll x (p :: ps) = Bool.xor (p.1.eval x) (xorAll x ps) := rfl

/-- `pairDepth` on a cons cell. -/
private theorem pairDepth_cons (p : Circuit n × Circuit n)
    (ps : List (Circuit n × Circuit n)) :
    pairDepth (p :: ps) = max (max p.1.depth p.2.depth) (pairDepth ps) := rfl

/-- `pairFanin` on a cons cell. -/
private theorem pairFanin_cons (p : Circuit n × Circuit n)
    (ps : List (Circuit n × Circuit n)) :
    pairFanin (p :: ps) = max (max p.1.maxFanin p.2.maxFanin) (pairFanin ps) := rfl

/-- `xorNode` costs two levels of depth. -/
private theorem pairDepth_xorNode (p q : Circuit n × Circuit n) :
    max (xorNode p q).1.depth (xorNode p q).2.depth
      ≤ 2 + max (max p.1.depth p.2.depth) (max q.1.depth q.2.depth) := by
  simp only [xorNode, Circuit.depth_node, Circuit.maxDepth_cons, Circuit.maxDepth_nil]
  omega

/-- `xorNode` introduces only fan-in-2 gates. -/
private theorem pairFanin_xorNode (p q : Circuit n × Circuit n) :
    max (xorNode p q).1.maxFanin (xorNode p q).2.maxFanin
      ≤ max 2 (max (max p.1.maxFanin p.2.maxFanin) (max q.1.maxFanin q.2.maxFanin)) := by
  simp only [xorNode, Circuit.maxFanin_node, Circuit.maxFaninL_cons, Circuit.maxFaninL_nil,
    List.length_cons, List.length_nil]
  omega

/-- Pair adjacent entries and XOR each pair. -/
private def xorPairUp : List (Circuit n × Circuit n) → List (Circuit n × Circuit n)
  | [] => []
  | [p] => [p]
  | p :: q :: ps => xorNode p q :: xorPairUp ps

/-- Pairing halves the list, rounding up. -/
private theorem length_xorPairUp :
    ∀ ps : List (Circuit n × Circuit n), (xorPairUp ps).length = (ps.length + 1) / 2
  | [] => by simp [xorPairUp]
  | [_] => by simp [xorPairUp]
  | _ :: _ :: ps => by
      have := length_xorPairUp ps
      simp only [xorPairUp, List.length_cons] at *
      omega

/-- Pairing preserves duality. -/
private theorem isDual_xorPairUp (x : Fin n → Bool) :
    ∀ ps : List (Circuit n × Circuit n), (∀ p ∈ ps, IsDual x p) →
      ∀ p ∈ xorPairUp ps, IsDual x p
  | [], _ => by simp [xorPairUp]
  | [p], h => by simpa [xorPairUp] using h p (by simp)
  | p :: q :: ps, h => by
      have ih := isDual_xorPairUp x ps (fun r hr => h r (by simp [hr]))
      intro r hr
      rcases List.mem_cons.mp (by simpa [xorPairUp] using hr) with rfl | hr'
      · exact xorNode_isDual (h p (by simp)) (h q (by simp))
      · exact ih r hr'

/-- Pairing preserves the overall XOR. -/
private theorem xorAll_xorPairUp (x : Fin n → Bool) :
    ∀ ps : List (Circuit n × Circuit n), (∀ p ∈ ps, IsDual x p) →
      xorAll x (xorPairUp ps) = xorAll x ps
  | [], _ => rfl
  | [_], _ => rfl
  | p :: q :: ps, h => by
      have ih := xorAll_xorPairUp x ps (fun r hr => h r (by simp [hr]))
      simp only [xorPairUp, xorAll_cons]
      rw [xorNode_eval (h p (by simp)) (h q (by simp)), ih, Bool.xor_assoc]

/-- Pairing adds two to the depth. -/
private theorem pairDepth_xorPairUp :
    ∀ ps : List (Circuit n × Circuit n), pairDepth (xorPairUp ps) ≤ 2 + pairDepth ps
  | [] => by simp [xorPairUp, pairDepth]
  | [p] => by simp [xorPairUp, pairDepth_cons]
  | p :: q :: ps => by
      have ih := pairDepth_xorPairUp ps
      have hn := pairDepth_xorNode p q
      simp only [xorPairUp, pairDepth_cons]
      omega

/-- Pairing introduces only fan-in-2 gates. -/
private theorem pairFanin_xorPairUp :
    ∀ ps : List (Circuit n × Circuit n), pairFanin (xorPairUp ps) ≤ max 2 (pairFanin ps)
  | [] => by simp [xorPairUp, pairFanin]
  | [p] => by simp [xorPairUp, pairFanin_cons]
  | p :: q :: ps => by
      have ih := pairFanin_xorPairUp ps
      have hn := pairFanin_xorNode p q
      simp only [xorPairUp, pairFanin_cons]
      omega

/-- Repeatedly pair and XOR, `k` rounds at most.  The zero-fuel branch is unreachable for
`ps ≠ []`: every lemma about it, and `xorTree` itself, supply `ps.length ≤ k`. -/
private def xorFuel : ℕ → List (Circuit n × Circuit n) → Circuit n × Circuit n
  | 0, _ => (Circuit.node false [], Circuit.node true [])
  | _ + 1, [] => (Circuit.node false [], Circuit.node true [])
  | _ + 1, [p] => p
  | k + 1, p :: q :: ps => xorFuel k (xorPairUp (p :: q :: ps))

/-- The XOR tree computes the XOR, and its second component the negation. -/
private theorem xorFuel_eval (x : Fin n → Bool) :
    ∀ (k : ℕ) (ps : List (Circuit n × Circuit n)), ps.length ≤ k →
      (∀ p ∈ ps, IsDual x p) →
      (xorFuel k ps).1.eval x = xorAll x ps ∧ IsDual x (xorFuel k ps)
  | 0, [], _, _ => by
      refine ⟨?_, ?_⟩ <;> simp [xorFuel, xorAll, IsDual, Circuit.eval]
  | 0, _ :: _, h, _ => by simp at h
  | _ + 1, [], _, _ => by
      refine ⟨?_, ?_⟩ <;> simp [xorFuel, xorAll, IsDual, Circuit.eval]
  | _ + 1, [p], _, h => by
      refine ⟨?_, h p (by simp)⟩
      show p.1.eval x = _
      simp [xorAll]
  | k + 1, p :: q :: ps, h, hd => by
      have hp := length_xorPairUp (p :: q :: ps)
      have hlen : (xorPairUp (p :: q :: ps)).length ≤ k := by
        simp only [List.length_cons] at h hp ⊢; omega
      have ih := xorFuel_eval x k _ hlen (isDual_xorPairUp x _ hd)
      show ((xorFuel k (xorPairUp (p :: q :: ps))).1.eval x = _) ∧ _
      rw [ih.1, xorAll_xorPairUp x _ hd]
      exact ⟨rfl, ih.2⟩

/-- The XOR tree has depth at most `2⌈log₂ m⌉ + 2` over its leaves. -/
private theorem xorFuel_depth :
    ∀ (k : ℕ) (ps : List (Circuit n × Circuit n)), ps.length ≤ k →
      max (xorFuel k ps).1.depth (xorFuel k ps).2.depth
        ≤ pairDepth ps + 2 * Nat.clog 2 ps.length + 2
  | 0, [], _ => by simp [xorFuel, Circuit.depth_node, Circuit.maxDepth_nil, pairDepth]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [xorFuel, Circuit.depth_node, Circuit.maxDepth_nil, pairDepth]
  | _ + 1, [p], _ => by
      show max p.1.depth p.2.depth ≤ _
      rw [pairDepth_cons]
      simp [pairDepth]
  | k + 1, p :: q :: ps, h => by
      have hp := length_xorPairUp (p :: q :: ps)
      have hlen : (xorPairUp (p :: q :: ps)).length ≤ k := by
        simp only [List.length_cons] at h hp ⊢; omega
      have ih := xorFuel_depth k _ hlen
      have hd := pairDepth_xorPairUp (p :: q :: ps)
      have hclog : Nat.clog 2 (p :: q :: ps).length
          = Nat.clog 2 ((xorPairUp (p :: q :: ps)).length) + 1 := by
        rw [hp]
        have := Nat.clog_of_two_le (b := 2) (n := (p :: q :: ps).length)
          (by norm_num) (by simp)
        simpa using this
      show max (xorFuel k (xorPairUp (p :: q :: ps))).1.depth
        (xorFuel k (xorPairUp (p :: q :: ps))).2.depth ≤ _
      omega

/-- The XOR tree has fan-in 2. -/
private theorem xorFuel_fanin :
    ∀ (k : ℕ) (ps : List (Circuit n × Circuit n)), ps.length ≤ k →
      max (xorFuel k ps).1.maxFanin (xorFuel k ps).2.maxFanin ≤ max 2 (pairFanin ps)
  | 0, [], _ => by simp [xorFuel, Circuit.maxFanin_node, Circuit.maxFaninL_nil]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [xorFuel, Circuit.maxFanin_node, Circuit.maxFaninL_nil]
  | _ + 1, [p], _ => by
      show max p.1.maxFanin p.2.maxFanin ≤ _
      rw [pairFanin_cons]
      omega
  | k + 1, p :: q :: ps, h => by
      have hp := length_xorPairUp (p :: q :: ps)
      have hlen : (xorPairUp (p :: q :: ps)).length ≤ k := by
        simp only [List.length_cons] at h hp ⊢; omega
      have ih := xorFuel_fanin k _ hlen
      have hf := pairFanin_xorPairUp (p :: q :: ps)
      show max (xorFuel k (xorPairUp (p :: q :: ps))).1.maxFanin
        (xorFuel k (xorPairUp (p :: q :: ps))).2.maxFanin ≤ _
      omega

/-- The balanced XOR tree over a list of dual pairs. -/
private def xorTree (ps : List (Circuit n × Circuit n)) : Circuit n × Circuit n :=
  xorFuel ps.length ps

/-- The literal pairs `(xᵢ, ¬xᵢ)`, one per input bit. -/
private def parityPairs (m : ℕ) : List (Circuit m × Circuit m) :=
  (List.finRange m).map fun i => (Circuit.lit ⟨i, true⟩, Circuit.lit ⟨i, false⟩)

/-- Literal pairs are dual. -/
private theorem isDual_parityPairs (x : Fin n → Bool) :
    ∀ p ∈ parityPairs n, IsDual x p := by
  intro p hp
  simp only [parityPairs, List.mem_map] at hp
  obtain ⟨i, _, rfl⟩ := hp
  simp [IsDual, Circuit.eval, Lit.eval]

/-- Literal pairs have depth `0`. -/
private theorem pairDepth_parityPairs : pairDepth (parityPairs n) = 0 := by
  simp only [parityPairs]
  induction List.finRange n with
  | nil => rfl
  | cons i l ih => simp [pairDepth_cons, ih, Circuit.depth]

/-- Literal pairs have fan-in `0`. -/
private theorem pairFanin_parityPairs : pairFanin (parityPairs n) = 0 := by
  simp only [parityPairs]
  induction List.finRange n with
  | nil => rfl
  | cons i l ih => simp [pairFanin_cons, ih, Circuit.maxFanin]

/-- Literal pairs number one per input bit. -/
private theorem length_parityPairs : (parityPairs n).length = n := by
  simp [parityPairs]

/-- The XOR over literal pairs is the XOR of the input bits. -/
private theorem xorAll_parityPairs (x : Fin n → Bool) :
    xorAll x (parityPairs n)
      = (List.finRange n).foldr (fun i acc => Bool.xor (x i) acc) false := by
  simp only [parityPairs]
  induction List.finRange n with
  | nil => rfl
  | cons i l ih =>
      simp only [List.map_cons, xorAll_cons, List.foldr_cons, ih]
      simp [Circuit.eval, Lit.eval]

/-- The balanced binary XOR tree computing `PARITY` on `n` bits.  [AB09, Ex 6.26] -/
def parityCircuit (m : ℕ) : Circuit m := (xorTree (parityPairs m)).1

/-- `parityCircuit` computes the XOR of all input bits. -/
theorem parityCircuit_eval (x : Fin n → Bool) :
    (parityCircuit n).eval x
      = (List.finRange n).foldr (fun i acc => Bool.xor (x i) acc) false := by
  rw [parityCircuit, xorTree,
    (xorFuel_eval x _ (parityPairs n) (le_refl _) (isDual_parityPairs x)).1,
    xorAll_parityPairs]

/-- `parityCircuit` has fan-in `2`. -/
theorem parityCircuit_maxFanin_le : (parityCircuit n).maxFanin ≤ 2 := by
  have h := xorFuel_fanin (parityPairs n).length (parityPairs n) (le_refl _)
  rw [pairFanin_parityPairs] at h
  simp only [Nat.max_eq_left (Nat.zero_le 2)] at h
  exact le_trans (le_max_left _ _) h

/-- `parityCircuit` has depth `O(log n)`. -/
theorem parityCircuit_depth_le : (parityCircuit n).depth ≤ 4 * (Nat.log 2 n + 1) := by
  have h1 : (parityCircuit n).depth
      ≤ pairDepth (parityPairs n) + 2 * Nat.clog 2 (parityPairs n).length + 2 :=
    le_trans (le_max_left _ _)
      (xorFuel_depth (parityPairs n).length (parityPairs n) (le_refl _))
  rw [pairDepth_parityPairs, length_parityPairs] at h1
  have hc : Nat.clog 2 n ≤ Nat.log 2 n + 1 := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    exact Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) n)
  omega

/-- `parityCircuit` has polynomial size, by the depth bound and fan-in `2`. -/
theorem parityCircuit_size_le : (parityCircuit n).size ≤ 32 * (n + 1) ^ 4 := by
  have hd := parityCircuit_depth_le (n := n)
  have hs := Circuit.size_succ_le_two_pow (parityCircuit n) parityCircuit_maxFanin_le
  have hmono : (2 : ℕ) ^ ((parityCircuit n).depth + 1) ≤ 2 ^ (4 * (Nat.log 2 n + 1) + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlog : (2 : ℕ) ^ (Nat.log 2 n + 1) ≤ 2 * (n + 1) := by
    have := Nat.pow_log_le_add_one 2 n
    rw [pow_succ]
    omega
  have hfin : (2 : ℕ) ^ (4 * (Nat.log 2 n + 1) + 1) ≤ 32 * (n + 1) ^ 4 := by
    calc (2 : ℕ) ^ (4 * (Nat.log 2 n + 1) + 1)
        = 2 * (2 ^ (Nat.log 2 n + 1)) ^ 4 := by
          rw [pow_succ, ← pow_mul, Nat.mul_comm 4 (Nat.log 2 n + 1)]
          ring
      _ ≤ 2 * (2 * (n + 1)) ^ 4 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hlog 4)
      _ = 32 * (n + 1) ^ 4 := by ring
  omega

/-- `PARITY` on the empty input is `false`. -/
theorem parityCircuit_eval_zero (x : Fin 0 → Bool) : (parityCircuit 0).eval x = false := by
  rw [parityCircuit_eval]; rfl

/-- `PARITY` on a one-bit input is that bit; note `Nat.log 2 1 = 0`, so the depth bound
`4 * (Nat.log 2 n + 1)` is the constant `4` here and at `n = 0`, not `0`. -/
theorem parityCircuit_eval_one (x : Fin 1 → Bool) : (parityCircuit 1).eval x = x 0 := by
  rw [parityCircuit_eval]; simp [List.finRange]

end BoolCircuit

/-- `PARITY = {x : x has an odd number of 1s}`.  [AB09, Ex 6.26] -/
def Language.parity : Language Bool := {w | w.count true % 2 = 1}

/-- `PARITY` membership is the iterated XOR of the word's letters. -/
theorem Language.mem_parity_iff (w : List Bool) :
    w ∈ Language.parity ↔ w.foldr Bool.xor false = true := by
  show w.count true % 2 = 1 ↔ _
  induction w with
  | nil => simp
  | cons b w ih =>
      cases b with
      | false => simpa [List.count_cons] using ih
      | true =>
          rcases Bool.eq_false_or_eq_true (w.foldr Bool.xor false) with hf | hf <;>
            rw [hf] at ih <;> simp_all <;> omega

/-- [AB09, Ex 6.26]: `PARITY ∈ NC¹`, via the balanced binary tree.

**Proof sketch.** `BoolCircuit.parityCircuit n` is the balanced binary tree whose leaves
are the `n` input bits and whose internal gates take the XOR of their two children.  Since
this circuit model negates only at literals, each node carries a *pair* — a circuit for the
XOR of its leaves and a circuit for its complement — and `xorNode` builds the pair for a
parent from those of its two children as `(a ∧ b') ∨ (a' ∧ b)` and `(a ∧ b) ∨ (a' ∧ b')`,
costing two levels of depth.  Halving the list `⌈log₂ n⌉` times therefore gives depth
`2⌈log₂ n⌉ + 2 ≤ 4(log₂ n + 1)` and fan-in `2`; polynomial size then follows from
`Circuit.size_succ_le_two_pow`, since a fan-in-2 tree of depth `d` has fewer than `2^(d+1)`
nodes.  Reading the tree at word length `|w|` and folding `List.finRange_map_get` gives the
XOR of `w`'s letters, which is `1` exactly when `w` has an odd number of `1`s. -/
theorem Language.parity_inNC_one : Language.parity.InNC 1 := by
  refine ⟨⟨BoolCircuit.parityCircuit⟩, fun n => BoolCircuit.parityCircuit_maxFanin_le,
    ⟨32, 4, fun n => BoolCircuit.parityCircuit_size_le⟩,
    ⟨4, fun n => by simpa using BoolCircuit.parityCircuit_depth_le⟩, ?_⟩
  ext w
  rw [BoolCircuit.TreeCircuitFamily.mem_language_iff, BoolCircuit.parityCircuit_eval,
    ← List.foldr_map, List.finRange_map_get, ← Language.mem_parity_iff]

## ===== TCSlib/Complexity/CircuitComplexity/SizeClasses.lean =====

/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.Complexity.CircuitComplexity.PPoly

/-!
# `SIZE` monotonicity, and Arora–Barak Example 6.3

## Main definitions

* `Language.allOnes` — the language `{1ⁿ}` of [AB09, Ex 6.3], part 1.
* `BoolCircuit.andGateOp` — the unbounded fan-in `AND` gate.
* `BoolCircuit.allOnesCircuit` / `BoolCircuit.allOnesFamily` — the circuit and family deciding it.

## Main results

* `Language.InSIZE.mono` — `SIZE(T) ⊆ SIZE(T')` when `T ≤ T'` pointwise.
* `Language.InSIZE.inPPoly` — `SIZE(T) ⊆ P/poly` when `T n ≤ a * (n + 1) ^ k`.
* `Language.allOnes_inSIZE_linear` / `_inPPoly` — `{1ⁿ}` is linear-size, so in `P/poly`.

## Divergences from Arora–Barak Example 6.3

AB's circuit is a tree of fan-in-2 `AND` gates (`n - 1` non-input vertices, depth
`⌈log₂ n⌉`); ours is one unbounded `AND` gate (`size = 1`, depth `1`), the same
function in the unbounded-fan-in basis `PPoly.lean` fixes — both linear-size,
which is all AB claims. AB writes `{1ⁿ : n ∈ ℤ}`; we read that `ℤ` as `ℕ`, since
`1ⁿ` names no word for `n < 0`, so `n = 0` is in and the empty `AND` gate, being
the empty product `1`, makes `C₀` accept `ε = 1⁰`. Words are `List Bool`, so AB's
letter `1` is `true`, and `finTwoEquiv` converts at the circuit boundary.

## Deferred: Theorem 6.6, `P ⊆ P/poly`

Not formalized, and not stubbed with `sorry`. AB simulates an oblivious Turing
machine (Remark 1.7) by a circuit, Cook–Levin style, which needs a machine model,
the class `P`, and the oblivious-simulation theorem. All three now live on this
branch (`TuringMachine/` with `Robustness/ObliviousSchedule.lean`, and
`ClassP/`); the bridge theorem is tracked in `backlog.md` §3.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- `SIZE(T) ⊆ SIZE(T')` whenever `T ≤ T'` pointwise. -/
theorem Language.InSIZE.mono {T T' : ℕ → ℕ} {L : Language Bool} (hL : L.InSIZE T)
    (h : ∀ n, T n ≤ T' n) : L.InSIZE T' := by
  obtain ⟨C, hG, hS, hC⟩ := hL
  exact ⟨C, hG, fun n => (hS n).trans (h n), hC⟩

/-- A language in `SIZE(T)` for a polynomially bounded `T` is in `P/poly`. -/
theorem Language.InSIZE.inPPoly {T : ℕ → ℕ} {L : Language Bool} {a k : ℕ}
    (hL : L.InSIZE T) (hT : ∀ n, T n ≤ a * (n + 1) ^ k) : L.InPPoly :=
  ⟨a, k, hL.mono hT⟩

/-- `finTwoEquiv` sends `true`, and only `true`, to `1`. -/
private theorem finTwoEquiv_symm_eq_one_iff (b : Bool) :
    finTwoEquiv.symm b = 1 ↔ b = true := by
  cases b <;> decide

/-- `{1ⁿ : n ∈ ℕ}`, the words all of whose letters are `true`.  [AB09, Ex 6.3] -/
def Language.allOnes : Language Bool := {w | ∀ b ∈ w, b = true}

/-- `Language.allOnes` is the set of words `1ⁿ`. -/
theorem Language.mem_allOnes_iff (w : List Bool) :
    w ∈ Language.allOnes ↔ w = List.replicate w.length true :=
  List.eq_replicate_length.symm

namespace BoolCircuit

open FeedForward

/-- The unbounded fan-in `AND` gate on `w` inputs, in the shape used by `stdGateOps`. -/
def andGateOp (w : ℕ) : GateOp (Fin 2) := ⟨Fin w, fun x => ∏ i, x i⟩

/-- `andGateOp w` is one of the `stdGateOps`. -/
theorem andGateOp_mem_stdGateOps (w : ℕ) : andGateOp w ∈ stdGateOps :=
  Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨w, rfl⟩)

/-- Over `Fin 2` a product is `1` exactly when every factor is. -/
theorem prod_fin_two_eq_one_iff {ι : Type*} [Fintype ι] (x : ι → Fin 2) :
    ∏ i, x i = 1 ↔ ∀ i, x i = 1 := by
  classical
  constructor
  · intro h i
    rw [← Finset.mul_prod_erase _ x (Finset.mem_univ i)] at h
    exact (by decide : ∀ a b : Fin 2, a * b = 1 → a = 1) _ _ h
  · exact fun h => Finset.prod_eq_one fun i _ => h i

/-- The two layers of `allOnesCircuit n`: the `n` inputs, then the single output. -/
private def allOnesNodes (n : ℕ) : Fin 2 → Type
  | ⟨0, _⟩ => Fin n
  | ⟨_ + 1, _⟩ => Unit

/-- The depth-1 circuit taking the `AND` of all `n` inputs.  [AB09, Ex 6.3] -/
def allOnesCircuit (n : ℕ) : FeedForward (Fin 2) (Fin n) Unit where
  depth := 1
  nodes := allOnesNodes n
  gates := fun d => match d with
    | ⟨0, _⟩ => fun _ => ⟨andGateOp n, fun i => i⟩
    | ⟨_ + 1, h⟩ => absurd h (by omega)
  nodes_zero := rfl
  nodes_last := rfl

/-- The circuit outputs the product, that is the `AND`, of its inputs. -/
@[simp]
theorem allOnesCircuit_eval₁ (n : ℕ) (x : Fin n → Fin 2) :
    (allOnesCircuit n).eval₁ x = ∏ i, x i := rfl

/-- The circuit has a single non-input node, so `size = 1` for every `n`. -/
theorem allOnesCircuit_size (n : ℕ) : (allOnesCircuit n).size = 1 := by
  show Nat.card (Σ _ : Fin 1, Unit) = 1
  simp

/-- The family of [AB09, Ex 6.3], part 1. -/
def allOnesFamily : CircuitFamily where
  circuit := allOnesCircuit
  finite n := by
    rintro ⟨_ | v, hv⟩
    · exact inferInstanceAs (Finite (Fin n))
    · exact inferInstanceAs (Finite Unit)

/-- The family's length-`n` circuit is `allOnesCircuit n`. -/
@[simp]
theorem allOnesFamily_circuit (n : ℕ) : allOnesFamily.circuit n = allOnesCircuit n := rfl

/-- The family uses only `stdGateOps`. -/
theorem allOnesFamily_onlyUsesGates : allOnesFamily.OnlyUsesGates stdGateOps := by
  intro n
  show (allOnesCircuit n).onlyUsesGates stdGateOps
  rintro ⟨_ | d, hd⟩ u
  · exact andGateOp_mem_stdGateOps n
  · exact absurd hd (by have : (allOnesCircuit n).depth = 1 := rfl; omega)

/-- The family decides exactly `Language.allOnes`. -/
theorem allOnesFamily_language : allOnesFamily.language = Language.allOnes := by
  ext w
  simp only [CircuitFamily.mem_language_iff, allOnesFamily_circuit, allOnesCircuit_eval₁,
    prod_fin_two_eq_one_iff, finTwoEquiv_symm_eq_one_iff, Language.allOnes,
    List.get_eq_getElem, List.forall_mem_iff_getElem]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.2⟩

end BoolCircuit

/-- `{1ⁿ} ∈ SIZE(1)`. -/
theorem Language.allOnes_inSIZE_one : Language.allOnes.InSIZE (fun _ => 1) :=
  ⟨BoolCircuit.allOnesFamily, BoolCircuit.allOnesFamily_onlyUsesGates,
    fun n => (BoolCircuit.allOnesCircuit_size n).le, BoolCircuit.allOnesFamily_language⟩

/-- [AB09, Ex 6.3], part 1: `{1ⁿ}` is decided by a linear-size circuit family. -/
theorem Language.allOnes_inSIZE_linear : Language.allOnes.InSIZE (fun n => n + 1) :=
  Language.allOnes_inSIZE_one.mono fun n => Nat.succ_le_succ n.zero_le

/-- [AB09, Ex 6.3], part 1: consequently `{1ⁿ} ∈ P/poly`. -/
theorem Language.allOnes_inPPoly : Language.allOnes.InPPoly :=
  Language.allOnes_inSIZE_linear.inPPoly (a := 1) (k := 1) fun n => by simp

## ===== TCSlib/Complexity/CircuitComplexity/UHalt.lean =====

/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import Mathlib.Computability.Halting
import TCSlib.Complexity.CircuitComplexity.UnaryLanguages

/-!
# Arora–Barak `UHALT`: an undecidable unary language in `P/poly`

## Main definitions

* `Nat.Partrec.Code.haltingSet` — the halting problem as a `Set ℕ`.
* `Language.uhalt` — AB's `UHALT`.

## Main results

* `Nat.Partrec.Code.not_computablePred_mem_haltingSet` — `haltingSet` is undecidable.
* `Language.not_computablePred_mem_unary` — `unary S` is undecidable when `S` is.
* `Language.uhalt_inPPoly` — `UHALT` is in `P/poly`.
* `Language.not_computablePred_mem_uhalt` — `UHALT` is undecidable.
* `Language.exists_le_allOnes_inPPoly_not_computablePred` — [AB09, p.110].

## Divergences from Arora–Barak p.110

AB writes `UHALT = {1ⁿ : n's binary expansion encodes a pair ⟨M, x⟩ such that M
halts on input x}`. The numbering is changed, the shape kept: `n` decodes to the
pair `(n.unpair.1, n.unpair.2)`, the first component read as a Gödel number
through `Denumerable.ofNat Nat.Partrec.Code`, the second as its input, and
"halts" is `Part.Dom` of `Nat.Partrec.Code.eval`. "Undecidable" is
`¬ ComputablePred (· ∈ L)`. `haltingSet` is a `Set ℕ`, not a language, so it
sits beside `Nat.Partrec.Code.eval` rather than in `Language`.

AB concludes `P ⊊ P/poly`. AB's route also needs Theorem 6.6 (`P ⊆ P/poly`);
the machine model, the class `P`, and the oblivious-simulation layer all live
on this branch now, and the bridge theorem is tracked in `backlog.md` §3. Only
the statable half is here: `exists_le_allOnes_inPPoly_not_computablePred`.
The undecidability half is not reproved from AB: it is Mathlib's
`ComputablePred.halting_problem`, transported along the pairing.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Nat.Partrec.Code

/-- The halting problem as a set of naturals: `n` belongs when the code numbered
`n.unpair.1` halts on input `n.unpair.2`. -/
def haltingSet : Set ℕ :=
  {n | (eval (Denumerable.ofNat Code n.unpair.1) n.unpair.2).Dom}

/-- `haltingSet` is undecidable. -/
theorem not_computablePred_mem_haltingSet : ¬ ComputablePred (· ∈ haltingSet) := by
  intro h
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp h
  refine ComputablePred.halting_problem 0 (ComputablePred.computable_iff.mpr
    ⟨fun c => f (Nat.pair (Encodable.encode c) 0),
      hf.comp (Primrec₂.natPair.to_comp.comp Computable.encode (Computable.const 0)), ?_⟩)
  funext c
  have h₀ := congrFun hfe (Nat.pair (Encodable.encode c) 0)
  simpa [haltingSet, Nat.unpair_pair, Denumerable.ofNat_encode] using h₀

end Nat.Partrec.Code

namespace Language

/-- `unary S` is undecidable whenever `S` is. -/
theorem not_computablePred_mem_unary {S : Set ℕ} (hS : ¬ ComputablePred (· ∈ S)) :
    ¬ ComputablePred (· ∈ unary S) := by
  intro h
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp h
  have hrep : Computable fun n : ℕ => List.replicate n true :=
    ((Primrec.list_map Primrec.list_range (Primrec.const true).to₂).of_eq
      fun n => by simp).to_comp
  refine hS (ComputablePred.computable_iff.mpr
    ⟨fun n => f (List.replicate n true), hf.comp hrep, ?_⟩)
  funext n
  rw [← replicate_mem_unary_iff (S := S) n]
  exact congrFun hfe _

/-- `UHALT`: the words `1ⁿ` whose length codes a halting computation.
[AB09, p.110] -/
def uhalt : Language Bool := unary Nat.Partrec.Code.haltingSet

/-- `UHALT` is in `P/poly`. -/
theorem uhalt_inPPoly : uhalt.InPPoly := unary_inPPoly _

/-- `UHALT` is undecidable. -/
theorem not_computablePred_mem_uhalt : ¬ ComputablePred (· ∈ uhalt) :=
  not_computablePred_mem_unary Nat.Partrec.Code.not_computablePred_mem_haltingSet

/-- Some unary language is in `P/poly` and is not computable.  [AB09, p.110] -/
theorem exists_le_allOnes_inPPoly_not_computablePred :
    ∃ L : Language Bool, L ≤ allOnes ∧ L.InPPoly ∧ ¬ ComputablePred (· ∈ L) :=
  ⟨uhalt, unary_le_allOnes _, uhalt_inPPoly, not_computablePred_mem_uhalt⟩

end Language

## ===== TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean =====

/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.Complexity.CircuitComplexity.SizeClasses

/-!
# Arora–Barak Claim 6.8: every unary language is in `P/poly`

## Main definitions

* `Language.unary` — the language `{1ⁿ : n ∈ S}`.
* `BoolCircuit.notGateOp` / `BoolCircuit.constZeroCircuit` — the `NOT` gate and the circuit that
  outputs `0` on every input.
* `BoolCircuit.unaryFamily` — [AB09, Claim 6.8]'s circuit family for a unary `L`.

## Main results

* `Language.le_allOnes_iff` — `L ≤ Language.allOnes` says `L ⊆ {1ⁿ : n ∈ ℕ}`.
* `Language.mem_unary_iff`, `Language.unary_le_allOnes`,
  `Language.replicate_mem_unary_iff` — the `Language.unary` API.
* `Language.exists_le_allOnes` — one unary language per `S : Set ℕ`.
* `BoolCircuit.unaryFamily_language` — for a unary `L`, the family decides exactly `L`.
* `Language.inSIZE_two_of_le_allOnes` — a unary language is in `SIZE(2)`.
* `Language.inPPoly_of_le_allOnes` / `Language.unary_inPPoly` — [AB09, Claim 6.8],
  in general and for `Language.unary`.

## Design

`stdGateOps` has no primitive constant-**false** operation (`andGateOp 0`, the
empty product, is constant *one*), so `constZeroCircuit` builds false out of the
two operations it uses: the empty `AND` is the empty product `1`, and `NOT` of that is `0`.
Hence depth `2` and size `2`.

Whether `1ⁿ ∈ L` is in general undecidable, so `unaryFamily` chooses between the
two branches by `Classical.propDecidable`. The per-length choice is what makes Claim 6.8
true, and is how AB then puts an undecidable language in `P/poly`.

`Language` has a `CompleteAtomicBooleanAlgebra` instance but no `HasSubset`, so
AB's `L ⊆ {1ⁿ : n ∈ ℕ}` is written `L ≤ Language.allOnes`.

AB describes a family of linear size; ours has size at most `2` at every length (`1` on the all-ones branch), so
`Language.inSIZE_two_of_le_allOnes` states the constant bound and Claim 6.8
follows from it with `a = 2`, `k = 0`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- A language is below `Language.allOnes` exactly when all its words are `1ⁿ`. -/
theorem Language.le_allOnes_iff (L : Language Bool) :
    L ≤ Language.allOnes ↔ ∀ w ∈ L, ∃ n, w = List.replicate n true := by
  constructor
  · intro h w hw
    exact ⟨w.length, (Language.mem_allOnes_iff w).mp (h hw)⟩
  · intro h w hw
    obtain ⟨n, rfl⟩ := h w hw
    exact fun b hb => List.eq_of_mem_replicate hb

/-- The unary language `{1ⁿ : n ∈ S}`. -/
def Language.unary (S : Set ℕ) : Language Bool :=
  {w | w ∈ Language.allOnes ∧ w.length ∈ S}

/-- Membership in `unary S` is being all ones and having length in `S`. -/
theorem Language.mem_unary_iff {S : Set ℕ} (w : List Bool) :
    w ∈ Language.unary S ↔ w ∈ Language.allOnes ∧ w.length ∈ S := Iff.rfl

/-- `unary S` is a unary language. -/
theorem Language.unary_le_allOnes (S : Set ℕ) : Language.unary S ≤ Language.allOnes :=
  fun _ hw => hw.1

/-- `1ⁿ` belongs to `unary S` exactly when `n ∈ S`. -/
theorem Language.replicate_mem_unary_iff {S : Set ℕ} (n : ℕ) :
    List.replicate n true ∈ Language.unary S ↔ n ∈ S := by
  rw [Language.mem_unary_iff, List.length_replicate]
  exact and_iff_right fun b hb => List.eq_of_mem_replicate hb

/-- For every `S : Set ℕ` some unary language contains exactly the words `1ⁿ`
with `n ∈ S`. -/
theorem Language.exists_le_allOnes (S : Set ℕ) :
    ∃ L : Language Bool, L ≤ Language.allOnes ∧
      ∀ n, List.replicate n true ∈ L ↔ n ∈ S :=
  ⟨Language.unary S, Language.unary_le_allOnes S,
    fun n => Language.replicate_mem_unary_iff n⟩

namespace BoolCircuit

open FeedForward

/-- The `NOT` gate, in the shape used by `stdGateOps`. -/
def notGateOp : GateOp (Fin 2) := ⟨Fin 1, fun x => 1 - x 0⟩

/-- `notGateOp` is one of the `stdGateOps`. -/
theorem notGateOp_mem_stdGateOps : notGateOp ∈ stdGateOps :=
  Set.mem_union_left _ (Set.mem_insert_iff.mpr (Or.inr rfl))

/-- The three layers of `constZeroCircuit n`: the `n` inputs, then two
singleton layers. -/
private def constZeroNodes (n : ℕ) : Fin 3 → Type
  | ⟨0, _⟩ => Fin n
  | ⟨_ + 1, _⟩ => Unit

/-- The depth-2 circuit computing the constant `0` on `n` inputs. -/
def constZeroCircuit (n : ℕ) : FeedForward (Fin 2) (Fin n) Unit where
  depth := 2
  nodes := constZeroNodes n
  gates := fun d => match d with
    | ⟨0, _⟩ => fun _ => ⟨andGateOp 0, fun i => i.elim0⟩
    | ⟨1, _⟩ => fun _ => ⟨notGateOp, fun _ => ()⟩
    | ⟨_ + 2, h⟩ => absurd h (by omega)
  nodes_zero := rfl
  nodes_last := rfl

/-- The circuit outputs `0` whatever its inputs are. -/
@[simp]
theorem constZeroCircuit_eval₁ (n : ℕ) (x : Fin n → Fin 2) :
    (constZeroCircuit n).eval₁ x = 0 := by
  show (1 : Fin 2) - 1 = 0
  rfl

/-- The circuit has two non-input nodes. -/
theorem constZeroCircuit_size (n : ℕ) : (constZeroCircuit n).size = 2 := by
  show Nat.card (Σ _ : Fin 2, Unit) = 2
  simp

/-- Every layer of the circuit is finite. -/
theorem constZeroCircuit_finite (n : ℕ) : (constZeroCircuit n).Finite := by
  rintro ⟨_ | v, hv⟩
  · exact inferInstanceAs (Finite (Fin n))
  · exact inferInstanceAs (Finite Unit)

/-- The circuit uses only `stdGateOps`. -/
theorem constZeroCircuit_onlyUsesGates (n : ℕ) :
    (constZeroCircuit n).onlyUsesGates stdGateOps := by
  rintro ⟨_ | _ | d, hd⟩ u
  · exact andGateOp_mem_stdGateOps 0
  · exact notGateOp_mem_stdGateOps
  · exact absurd hd (by have : (constZeroCircuit n).depth = 2 := rfl; omega)

open scoped Classical in
/-- [AB09, Claim 6.8]'s family for `L`: the all-ones circuit at the lengths `n`
with `1ⁿ ∈ L`, and the constant-`0` circuit at the others. -/
noncomputable def unaryFamily (L : Language Bool) : CircuitFamily where
  circuit n := if List.replicate n true ∈ L then allOnesCircuit n else constZeroCircuit n
  finite n := by
    by_cases h : List.replicate n true ∈ L
    · rw [if_pos h]; exact allOnesFamily.finite n
    · rw [if_neg h]; exact constZeroCircuit_finite n

/-- At a length with `1ⁿ ∈ L` the family uses `allOnesCircuit n`. -/
theorem unaryFamily_circuit_of_mem {L : Language Bool} {n : ℕ}
    (h : List.replicate n true ∈ L) : (unaryFamily L).circuit n = allOnesCircuit n :=
  if_pos h

/-- At a length with `1ⁿ ∉ L` the family uses `constZeroCircuit n`. -/
theorem unaryFamily_circuit_of_not_mem {L : Language Bool} {n : ℕ}
    (h : List.replicate n true ∉ L) : (unaryFamily L).circuit n = constZeroCircuit n :=
  if_neg h

/-- The family uses only `stdGateOps`. -/
theorem unaryFamily_onlyUsesGates (L : Language Bool) :
    (unaryFamily L).OnlyUsesGates stdGateOps := by
  intro n
  by_cases h : List.replicate n true ∈ L
  · rw [unaryFamily_circuit_of_mem h]; exact allOnesFamily_onlyUsesGates n
  · rw [unaryFamily_circuit_of_not_mem h]; exact constZeroCircuit_onlyUsesGates n

/-- Every circuit in the family has size at most `2`. -/
theorem unaryFamily_size_le (L : Language Bool) (n : ℕ) :
    ((unaryFamily L).circuit n).size ≤ 2 := by
  by_cases h : List.replicate n true ∈ L
  · rw [unaryFamily_circuit_of_mem h, allOnesCircuit_size]; omega
  · rw [unaryFamily_circuit_of_not_mem h, constZeroCircuit_size]

/-- For a unary `L`, the family decides exactly `L`.

**Proof sketch.** Every word of a unary `L` is a string of ones, so membership
in `L` splits into two independent conditions: `w` is all ones, and the all-ones
word of `w`'s own length lies in `L`.  Establishing that equivalence is the
first step.  Fix `w` and split on the second condition.  When it holds, the
family runs the all-ones circuit at length `w.length`, which accepts exactly the
all-ones words, so acceptance reduces to the first condition; when it fails, the
family runs the constant-`0` circuit, which accepts nothing, and both sides are
false.  The two cases exhaust the split. -/
theorem unaryFamily_language {L : Language Bool} (hL : L ≤ Language.allOnes) :
    (unaryFamily L).language = L := by
  have key : ∀ w : List Bool,
      w ∈ L ↔ w ∈ Language.allOnes ∧ List.replicate w.length true ∈ L := by
    intro w
    refine ⟨fun hw => ⟨hL hw, ?_⟩, ?_⟩
    · rwa [← (Language.mem_allOnes_iff w).mp (hL hw)]
    · rintro ⟨h₁, h₂⟩
      rwa [(Language.mem_allOnes_iff w).mp h₁]
  ext w
  rw [CircuitFamily.mem_language_iff, key w]
  by_cases h : List.replicate w.length true ∈ L
  · rw [unaryFamily_circuit_of_mem h]
    simp only [h, and_true]
    exact Set.ext_iff.mp allOnesFamily_language w
  · rw [unaryFamily_circuit_of_not_mem h, constZeroCircuit_eval₁]
    simp only [h, and_false, iff_false]
    decide

end BoolCircuit

/-- A unary language is decided by circuits of size `2`.  [AB09, Claim 6.8] -/
theorem Language.inSIZE_two_of_le_allOnes {L : Language Bool}
    (hL : L ≤ Language.allOnes) : L.InSIZE (fun _ => 2) :=
  ⟨BoolCircuit.unaryFamily L, BoolCircuit.unaryFamily_onlyUsesGates L, BoolCircuit.unaryFamily_size_le L,
    BoolCircuit.unaryFamily_language hL⟩

/-- Every unary language is in `P/poly`.  [AB09, Claim 6.8] -/
theorem Language.inPPoly_of_le_allOnes {L : Language Bool}
    (hL : L ≤ Language.allOnes) : L.InPPoly :=
  (Language.inSIZE_two_of_le_allOnes hL).inPPoly (a := 2) (k := 0) fun _ => by simp

/-- [AB09, Claim 6.8] for `Language.unary S`. -/
theorem Language.unary_inPPoly (S : Set ℕ) : (Language.unary S).InPPoly :=
  Language.inPPoly_of_le_allOnes (Language.unary_le_allOnes S)

## ===== TCSlib/Complexity/CircuitComplexity/Universal.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.FinRange
import TCSlib.Complexity.CircuitComplexity.Basic

/-!
# Universality: every Boolean function is computed by a circuit

[AB09, Claim 2.13], in the form [AB09, p.108] cites it in Chapter 6: every
`f : (Fin n → Bool) → Bool` is computed by a `BoolCircuit.Circuit n` of
explicitly bounded size.

## Main definitions

* `BoolCircuit.minterm v` — the `AND` of `n` literals that is true exactly at `v`.
* `BoolCircuit.universalCircuit f` — the `OR` of the minterms of `f`'s satisfying
  assignments.

## Main results

* `BoolCircuit.universalCircuit_eval` — `universalCircuit f` computes `f`.
* `BoolCircuit.universalCircuit_size` — its size is exactly `(n + 1)` times the number
  of satisfying assignments, plus one.
* `BoolCircuit.universalCircuit_size_le` — hence at most `2 ^ n * (n + 1) + 1`, a bound
  `BoolCircuit.universalCircuit_const_true_size` shows is attained.
* `BoolCircuit.exists_circuit_eval_eq_size_le` — the headline existence statement.

## Divergences from [AB09, Claim 2.13]

AB builds the **CNF** `⋀_{v : f v = 0} C_v` over the *falsifying* assignments;
we build the dual **DNF** `⋁_{v : f v = 1} T_v` over the satisfying ones.  Both
are one gate over at most `2ⁿ` gates of `n` literals; only the DNF is formalized
here.

**The constant is ours, not AB's.**  `n2ⁿ` is not an artifact of Chapter 2's
convention — it holds under both of AB's.  On `2ⁿ` clauses of `n` literals,
[AB09, Claim 2.13]'s count of `∧`/`∨` *symbols* is `(n-1)2ⁿ + (2ⁿ-1)`, that is
`n·2ⁿ - 1`; and under [AB09, Def 6.1] the same formula is a fan-in-2 DAG with
`n` shared sources, `n` shared `¬` gates, `(n-1)2ⁿ` binary `∨` and `2ⁿ-1`
binary `∧`, so `n·2ⁿ + 2n - 1` *vertices*.  The `∨` term is AB's own fan-in-2
expansion ([AB09, pp.107–108]: a fan-in-`f` gate becomes `f-1` binary ones),
not a lower bound on what a DAG needs.

`Circuit.size` measures a different object: nodes of an unbounded-fan-in *tree*.
Ours has `n·2ⁿ` literal leaves (nothing is shared, and a sign rides on the leaf
instead of a `¬` gate), `2ⁿ` minterm gates and one top gate — `2 ^ n * (n + 1) + 1`.
The leaves alone already come to within one of AB's whole symbol count, so they
are not what pushes us over; and a `k`-ary gate costs `1` here where AB's fan-in-2 expansion
costs `k-1`, a saving large enough that the net excess over `n·2ⁿ - 1` is only
`2ⁿ + 2`.  Same order as `n2ⁿ`, a larger number, and `2 ^ n * (n + 1) + 1` —
attained at `f ≡ true` — is what is proved here.  [AB09, Exercise 6.1]'s sharper
`O(2ⁿ/n)` is a different construction and is not attempted.

## Implementation notes

`Formulas.lean`'s `DNF` is not used as the intermediate: it is built on
`Literal`, a type distinct from `Basic.lean`'s `Lit`; it carries no size measure;
and TCSlib has no `DNF → Circuit` map (`NOrCircuit.toDNF` and `depth2OrToDNF`
both run the other way).  Using it would mean adding both.  `universalCircuit`
is `noncomputable` only because `Finset.toList` is.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-- The literal `⟨i, b⟩` holds at `x` exactly when `x i = b`. -/
private theorem lit_eval_iff (i : Fin n) (b : Bool) (x : Fin n → Bool) :
    (Lit.eval ⟨i, b⟩ x) = true ↔ x i = b := by
  cases b <;> simp [Lit.eval]

/-- Summed size of `l.map g` when every `g a` has size `k`. -/
private theorem foldr_size_map {α : Type*} {k : ℕ} (g : α → Circuit n)
    (hg : ∀ a, (g a).size = k) (l : List α) :
    (l.map g).foldr (fun c acc => c.size + acc) 0 = l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.foldr_cons, ih, hg a, List.length_cons]; ring

/-- The minterm of `v`: the `AND` over all `n` variables of the literal that `v`
satisfies.  At `n = 0` this is the empty conjunction. -/
def minterm (v : Fin n → Bool) : Circuit n :=
  .node true ((List.finRange n).map fun i => .lit ⟨i, v i⟩)

/-- `minterm v` accepts `v` and nothing else. -/
theorem minterm_eval_iff (v x : Fin n → Bool) :
    (minterm v).eval x = true ↔ x = v := by
  rw [minterm, Circuit.eval_node_true_iff]
  constructor
  · intro h
    funext i
    have hi := h (.lit ⟨i, v i⟩) (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    rw [Circuit.eval_lit] at hi
    exact (lit_eval_iff i (v i) x).mp hi
  · rintro rfl c hc
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
    rw [Circuit.eval_lit]
    exact (lit_eval_iff i (x i) x).mpr rfl

/-- A minterm is one gate over `n` leaves. -/
theorem minterm_size (v : Fin n → Bool) : (minterm v).size = n + 1 := by
  rw [minterm, Circuit.size, foldr_size_map _ (fun _ => by simp [Circuit.size]) (k := 1),
    List.length_finRange]
  ring

/-- The DNF of `f` as a circuit: the `OR` of the minterms of `f`'s satisfying
assignments.  [AB09, Claim 2.13] -/
noncomputable def universalCircuit (f : (Fin n → Bool) → Bool) : Circuit n :=
  .node false ((Finset.univ.filter fun v => f v = true).toList.map minterm)

/-- `universalCircuit f` computes `f`. -/
theorem universalCircuit_eval (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    (universalCircuit f).eval x = f x := by
  rw [Bool.eq_iff_iff, universalCircuit, Circuit.eval_node_false_iff]
  constructor
  · rintro ⟨c, hc, hce⟩
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    rw [(minterm_eval_iff v x).mp hce]
    simpa using Finset.mem_toList.mp hv
  · intro hx
    exact ⟨minterm x, List.mem_map.mpr ⟨x, Finset.mem_toList.mpr (by simpa using hx), rfl⟩,
      (minterm_eval_iff x x).mpr rfl⟩

/-- One `OR` gate over one `(n + 1)`-node minterm per satisfying assignment. -/
theorem universalCircuit_size (f : (Fin n → Bool) → Bool) :
    (universalCircuit f).size
      = (Finset.univ.filter fun v => f v = true).card * (n + 1) + 1 := by
  rw [universalCircuit, Circuit.size, foldr_size_map minterm minterm_size,
    Finset.length_toList]
  ring

/-- The size bound: `2 ^ n * (n + 1) + 1`, this construction's own constant. -/
theorem universalCircuit_size_le (f : (Fin n → Bool) → Bool) :
    (universalCircuit f).size ≤ 2 ^ n * (n + 1) + 1 := by
  rw [universalCircuit_size]
  refine Nat.add_le_add_right (Nat.mul_le_mul_right _ ?_) 1
  calc (Finset.univ.filter fun v => f v = true).card
      ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_filter_le _ _
    _ = 2 ^ n := by simp

/-- Every Boolean function on `n` bits is computed by a circuit of size at most
`2 ^ n * (n + 1) + 1`.  [AB09, Claim 2.13], as cited at [AB09, p.108] -/
theorem exists_circuit_eval_eq_size_le (f : (Fin n → Bool) → Bool) :
    ∃ c : Circuit n, (∀ x, c.eval x = f x) ∧ c.size ≤ 2 ^ n * (n + 1) + 1 :=
  ⟨universalCircuit f, universalCircuit_eval f, universalCircuit_size_le f⟩

/-! ### Degenerate cases -/

/-- No satisfying assignment: the circuit is the empty `OR`. -/
theorem universalCircuit_const_false :
    universalCircuit (fun _ : Fin n → Bool => false) = .node false [] := by
  simp [universalCircuit]

/-- Every assignment satisfying: the bound is attained. -/
theorem universalCircuit_const_true_size :
    (universalCircuit (fun _ : Fin n → Bool => true)).size = 2 ^ n * (n + 1) + 1 := by
  rw [universalCircuit_size]
  simp

/-- At `n = 0` a minterm is the empty conjunction, hence constantly `true`. -/
theorem minterm_eval_zero (v x : Fin 0 → Bool) : (minterm v).eval x = true :=
  (minterm_eval_iff v x).mpr (funext fun i => i.elim0)

end BoolCircuit

## ===== TCSlib/ComputationalModels.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.BooleanAnalysis.DecisionTree
import TCSlib.Complexity.CircuitComplexity.Basic
import TCSlib.Complexity.CircuitComplexity.FeedForward
import TCSlib.Complexity.CircuitComplexity.Formulas
import TCSlib.Complexity.CircuitComplexity.NCAC
import TCSlib.Complexity.CircuitComplexity.PPoly
import TCSlib.Complexity.Formulas.CNF
import TCSlib.Complexity.NPReductions.SATTo3SAT
import TCSlib.Complexity.TuringMachine.Deterministic
import TCSlib.Complexity.TuringMachine.Finite
import TCSlib.Complexity.TuringMachine.Nondeterministic
import TCSlib.Complexity.TuringMachine.Oracle

/-!
# Computational models: the catalog

Every model of computation in TCSlib, in one place. This facade imports each
model's defining file, so the catalog cannot silently rot: if a defining file
moves, this module stops compiling. `policy.md` §1 licenses a root-level
model *type* only when it is registered here; the model's operations and
lemmas still live in its own namespace.

Entries are alphabetical. Paths are relative to `TCSlib/`; machine files live
under `Complexity/`.

## Models

* `BoolCircuit.Circuit n` — tree-shaped Boolean circuits: unbounded fan-in
  AND/OR nodes over polarity-carrying literals
  (`Complexity/CircuitComplexity/Basic.lean`).
* `BoolCircuit.CircuitFamily` — non-uniform families of `FeedForward`
  circuits, one per input length; the carrier of `Language.InSIZE` and
  `P/poly` (`Complexity/CircuitComplexity/PPoly.lean`).
* `BoolCircuit.FeedForward α inp out` — layered DAG circuits over an
  arbitrary alphabet; the raw model enforces no gate basis, and classes impose
  `stdGateOps` via `OnlyUsesGates`
  (`Complexity/CircuitComplexity/FeedForward.lean`).
* `BoolCircuit.TreeCircuitFamily` — non-uniform families of tree circuits;
  the carrier of `NC` and `AC` (`Complexity/CircuitComplexity/NCAC.lean`).
* `CNF n` / `DNF n`, over `Literal n` and `Term n` — flat width-measured
  formulas for the switching-lemma development [OD14]
  (`Complexity/CircuitComplexity/Formulas.lean`).
* `DecisionTree n` — binary decision trees, with `dtDepth` the least depth
  computing a given function [OD14] (`BooleanAnalysis/DecisionTree.lean`).
* `FinNDTM` — bundled binary-choice nondeterministic machines; the carrier
  of `NTIME`, `NP`, `NEXP` (`Complexity/TuringMachine/Nondeterministic.lean`).
* `FinTM` — bundled deterministic machines; the carrier of `DTIME`, `P`,
  `EXP` (`Complexity/TuringMachine/Finite.lean`).
* `MultiTapeTM k Symbol State` — k-tape deterministic Turing machines with
  append-only output, the raw layer under `FinTM`
  (`Complexity/TuringMachine/Deterministic.lean`).
* `NDTM k Symbol State` — the raw layer under `FinNDTM`: binary-choice
  transitions, `List Bool` choice words
  (`Complexity/TuringMachine/Nondeterministic.lean`).
* `NPReductions.CNFFormula V` — the legacy variable-indexed CNF used by the
  SAT→3SAT reduction and the Tseitin encoding
  (`Complexity/NPReductions/SATTo3SAT.lean`).
* `OracleTM k Symbol State` — oracle machines with a dedicated query tape
  and one-step answers (`Complexity/TuringMachine/Oracle.lean`).
* `Std.Sat.CNF ℕ` — Lean core's clause-list CNF, the campaign's SAT/3SAT
  carrier; TCSlib's layer over it is in `Complexity/Formulas/CNF.lean`,
  with serialization in `Complexity/Formulas/CNFEncoding.lean`.

## Conversions

Model-to-model maps (pointers only — their files are not imported here):

* `BoolCircuit.Circuit.toFeedForward` — a semantic wrapper, not an embedding:
  the tree's evaluation becomes a single unrestricted first-layer gate, so only
  evaluation is preserved, never a gate basis
  (`Complexity/CircuitComplexity/FeedForward.lean`).
* `BoolCircuit.Circuit.tseitin` / `Circuit.toCNF` — circuits →
  equisatisfiable `NPReductions.CNFFormula`
  (`Complexity/CircuitComplexity/CircuitSat.lean`).
* `BoolCircuit.FeedForward.toCircuit` — DAG → tree unrolling, exponential
  in depth (`Complexity/CircuitComplexity/FeedForward.lean`).
* `FinTM.toFinNDTM` — deterministic machines as nondeterministic ones, in
  lockstep (`Complexity/TuringMachine/Nondeterministic.lean`).
* `LMN.NormalFormConversion` — normal-form tree circuits ↔ `CNF`/`DNF`
  formulas (`BooleanAnalysis/LMN/NormalFormConversion.lean`).
* `MultiTapeTM.toNDTM` — the raw-layer deterministic → nondeterministic
  embedding (`Complexity/TuringMachine/Nondeterministic.lean`).
* `OracleTM.ofMultiTapeTM` — plain machines as oracle machines that never
  query (`Complexity/TuringMachine/Oracle.lean`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [OD14] R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University
  Press, 2014.
-/

## ===== scripts/circuit_module_order.txt =====

TCSlib/Complexity/NPReductions/SATTo3SAT
TCSlib/Complexity/CircuitComplexity/Basic
TCSlib/Complexity/CircuitComplexity/Formulas
TCSlib/Complexity/CircuitComplexity/FeedForward
TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates
TCSlib/Complexity/CircuitComplexity/PPoly
TCSlib/Complexity/CircuitComplexity/SizeClasses
TCSlib/Complexity/CircuitComplexity/UnaryLanguages
TCSlib/Complexity/CircuitComplexity/UHalt
TCSlib/Complexity/CircuitComplexity/CircuitSat
TCSlib/Complexity/CircuitComplexity/Encoding
TCSlib/Complexity/CircuitComplexity/Universal
TCSlib/Complexity/CircuitComplexity/HardFunctions
TCSlib/Complexity/CircuitComplexity/Hierarchy
TCSlib/Complexity/CircuitComplexity/NCAC
TCSlib/Complexity/CircuitComplexity/Parity
TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree
TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitSize
TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra
TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction
TCSlib/BooleanAnalysis/RazborovSmolensky
TCSlib/Complexity/CircuitComplexity
