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
