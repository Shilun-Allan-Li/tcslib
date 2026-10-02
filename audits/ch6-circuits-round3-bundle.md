# External re-audit pack — Chapter-6 circuit surface, round 3

Audits commit `3ff0d76b` on `complexity/arora-barak-ch1`. Round 2
(pack `audits/ch6-circuits-reaudit-pack.md`, auditing `12ff3add`)
returned **0 blockers, 3 majors, 3 minors**
(`audits/ch6-circuits-reaudit-findings.md`, attached verbatim): round-1
major 2 and minors 5–7/9–10 discharged, the Def 6.1 / Def 6.2 verdicts
upgraded, and the three surviving majors all incomplete propagation of
round-1 repairs. All six round-2 findings were accepted; none contested.
The repairs — commit `3ff0d76b`, documentation only, zero Lean
statements changed — are itemized in the updated
`audits/ch6-circuits-resolutions.md` (attached), together with erratum
**R-E1** (this file's own round-1 "removed" claim, corrected per R2-1)
and erratum **R-E2** (the round-2 pack's "31", corrected to 32; total
55, matching the log). Both sent packs remain immutable.

## Repository-side attestations (maintainer, local machine — verify or challenge)

1. **Freeze.** `3ff0d76b` touches, relative to the audited `12ff3add`:
   six in-scope Lean files (`FeedForward`, `Hierarchy`, `PPoly`,
   `HardFunctions`, `Parity`, `UnaryLanguages`), the catalog,
   `backlog.md` §3's wrapper sentence, the resolutions file, and the
   newly committed `audits/logs/`. Docstrings and comment prose only;
   no `def`/`theorem`/`lemma`/`structure`/`instance` signature or body
   changed. Zero sorries in scope, as before.
2. **Exhaustive-propagation grep.** On the full `TCSlib/` tree plus the
   catalog and `backlog.md`, the retired phrases — "embedding is
   faithful", "is a weaker statement", "never rules out", "never
   discharge", "never a gate basis", "fan-in matters only", "embedded
   feedforward", "whose class is `Language.InSIZE`", "image size never
   mentions" — now have **zero occurrences**. (Round 2's majors were
   exactly phrase-survivals; this attestation is the systematic check
   round 1's repairs lacked.)
3. **Elaboration.** Post-repair fresh-olean sweep (run D of the
   resolutions appendix): the circuit order list from `FeedForward`
   onward plus the catalog, 20 modules, zero `error:` lines — the
   Switching/LMN trees import none of the six edited files. Lean 4.25.0
   / mathlib `029db123ddaa`. Raw logs for runs A–D are now committed
   under `audits/logs/`, addressing round 2's provenance caveat to the
   extent a bundle can.
4. **Policy.** Style lint: 0 FAIL / 0 WARN over `CircuitComplexity/`,
   unchanged.

## What round 3 asks

A closing verification round. The settled round-1/round-2 verdicts and
attack results stand unless a round-2 repair touched their text. Tasks:

1. **R2-1 … R2-3.** Judge whether each repair discharges the finding:
   the conversion overview and remaining "embedded" docstrings in
   `FeedForward.lean` (R2-1); the Main-results bullet in
   `Hierarchy.lean` and the fan-in sentence in `PPoly.lean` (R2-2); the
   "weaker statement" conclusion and the sharing warning in
   `HardFunctions.lean` (R2-3).
2. **R2-4 … R2-6.** Verify the two prose minors and the reconciled
   verification appendix (runs A–D, the disjointness claim for run C's
   two segments, erratum R-E2's arithmetic `22 + 32 + 1 = 55`, and the
   committed logs' consistency with the attested counts).
3. **Residual pass** over the newly written prose, including the two
   errata texts, under the round-1 severity scheme.

Findings to `audits/ch6-circuits-round3-findings.md`. The gate closes on
zero blockers/majors in this round.

## ===== audits/ch6-circuits-reaudit-findings.md =====

# Chapter 6 circuit surface: round-2 semantic re-audit

**Disposition: gate remains open.** This round finds **0 blockers, 3 majors, 3 minors, and 0 new advisory notes**. Round-1 major **2 is discharged**; majors **1, 3, and 4 are only partially repaired**. Each still has an explicit contrary claim in the attached source. The remaining repairs can be documentation-only.

Audited input: `ch6-circuits-reaudit-bundle.md`, representing commit `12ff3add` on `complexity/arora-barak-ch1`; audit date: 2026-10-02.

Bundle SHA-256: `e8ea98f2c305e26977413b76b96431091e2c79c70d78e1f7fad2fa40c9a11b8f`.

This is the commissioned verification round. The embedded round-1 findings, resolutions, repaired ledgers, relevant definitions, and associated declaration comments were examined. The settled guard attacks and Lean proofs were not re-audited. The bundle contains 18 attachment sections: two audit documents, 14 circuit Lean files including the facade, the catalog, and the sweep list. No input source was modified.

References such as `FeedForward.lean:131-134` mean `TCSlib/Complexity/CircuitComplexity/FeedForward.lean:131-134`; `CircuitComplexity.lean` denotes the facade at `TCSlib/Complexity/CircuitComplexity.lean`. Source line 1 is the first line after the attachment header and its separating blank line. `audits/ch6-circuits-reaudit-pack.md` denotes the bundle's opening verification pack, with its original line numbers.

The asserted documentation-only diff, commit provenance, fresh elaboration, and lint result remain maintainer attestations: the bundle does not contain the old source checkout, Git diff, or raw verification logs. The independently checkable sweep-count inconsistency is reported below; it is not evidence of a failed Lean proof.

## 1. Findings, in severity order

### R2-1. MAJOR — the false structural-embedding description survives verbatim

**Round-1 connection:** finding 1; repair incomplete.

**Locations:** `FeedForward.lean:131-134,285-293,328-341`; `audits/ch6-circuits-resolutions.md:17`.

The module introduction, conversion section heading, declaration docstring, and catalog now correctly call `Circuit.toFeedForward` a semantic wrapper. However, the conversion overview at lines 131-134 still says:

> the embedding is faithful. The FeedForward circuit has the same depth

and still gives the size bound `C.size * C.depth`, attributing it to padding shorter branches. Thus the resolutions record's assertion that the false bound was removed is contradicted by the attachment.

The original counterexample still applies. For a positive literal `C : Circuit 1`, the definitions give

$$
C.\mathrm{size}=1,\qquad C.\mathrm{depth}=0,
$$
$$
C.\mathrm{toFeedForward.depth}=0+1=1,
\qquad C.\mathrm{toFeedForward.size}=1,
$$
$$
1>1\cdot0=C.\mathrm{size}\,C.\mathrm{depth}.
$$

The construction at lines 294-309 installs the whole evaluation function, followed by identity gates; it does not copy source nodes or pad source branches. The formal resource theorems remain consistent with this construction. The later comments still say “embedded”/“embedding,” and line 335 incorrectly explains the extra depth as an extra input layer.

**Required repair:** Replace the overview at lines 131-134 with the same wrapper description used at lines 285-293. Describe the depth as one evaluation layer followed by `C.depth` identity layers. Change the surrounding “embedding” comments to “wrapper,” and correct the resolutions record. A structural circuit conversion is not required for closure.

### R2-2. MAJOR — fixed-size identification remains in the hierarchy summary

**Round-1 connection:** finding 3; repair incomplete.

**Locations:** `Hierarchy.lean:34-36,42-44`; `PPoly.lean:38-50`; `audits/ch6-circuits-resolutions.md:19`.

The new `PPoly` ledger explicitly distinguishes the local `InSIZE` from the book's fixed `SIZE(T)`, and the facade propagates that distinction correctly. But `Hierarchy.lean:34-36` still describes Theorem 6.22 as a theorem “whose class is `Language.InSIZE`.” That is the exact identification the repair was supposed to remove; it directly conflicts with lines 42-44 of the same module.

The recorded counterexample is decisive:

$$
\mathrm{Language.allOnes.InSIZE}(\mathrm{fun}\ \_\Rightarrow1)
$$

is supplied by `SizeClasses.lean:151-154`, whereas, at every length $n\ge2$, the book's input-counting convention requires

$$
|C|\ge n\ge2>1.
$$

There is a second surviving overstatement at `PPoly.lean:46-47`: “fan-in matters only under a depth restriction.” Fan-in also affects exact size budgets without a depth restriction. For example, conjunction of three variables uses one unbounded AND gate but cannot be computed using just one gate of fan-in at most two. The polynomial-union preservation claim does not justify that unrestricted sentence.

**Required repair:** Change the hierarchy summary to refer to the book's bounded-fan-in, input-counting DAG size classes, with local `InSIZE` identified only as a variant. Restrict the fan-in sentence to preservation of polynomial-size existence while allowing the budget to change. The new ledger and facade can otherwise stand.

### R2-3. MAJOR — the hard-function ledger still calls the local theorem weaker

**Round-1 connection:** finding 4; repair incomplete.

**Locations:** `HardFunctions.lean:35-53,59-62`; `CircuitComplexity.lean:54-56`; `audits/ch6-circuits-resolutions.md:20`.

The new quantitative paragraph correctly explains what the displayed conversion does and does not establish. The facade now correctly labels the result a tree-circuit analogue. However, the same ledger still concludes at lines 61-62:

> it is a weaker statement that happens to admit a larger constant.

This reasserts the statement-strength comparison rejected in round 1. It also contradicts the preceding qualification that neither quantified bound follows from the other by the given conversion.

The arithmetic remains:

$$
2^{20}=1{,}048{,}576,\qquad
\left\lfloor\frac{1{,}048{,}576}{200}\right\rfloor=5{,}242,
$$
$$
5{,}242-2\cdot20=5{,}202,
\qquad
\left\lfloor\frac{1{,}048{,}576}{25}\right\rfloor=41{,}943.
$$

Even granting the informal `S + 2n` simulation, the displayed book cutoff therefore supplies only the transferred tree cutoff 5,202, not 41,943. Model generality alone does not establish that the latter quantified theorem is weaker. This objection concerns the claimed comparison, not the truth of either theorem or the impossibility of every other comparison argument.

**Required repair:** Replace the surviving “weaker statement” sentence with: “This is a tree-counting analogue with a different cutoff; the displayed conversion establishes neither implication between the two stated bounds.” Likewise, phrase the adjacent sharing warning as absence of a transfer at the claimed cutoff, rather than saying tree hardness “never” rules out small DAGs. Keep the distinction between an available depth-dependent unrolling and an established polynomial simulation.

### R2-4. MINOR — the parity proof sketch still presents its depth bound as the depth

**Round-1 connection:** finding 8; repair incomplete.

**Locations:** `Parity.lean:32-34,217-221,387-398`; `audits/ch6-circuits-resolutions.md:24`.

The ledger and `xorFuel_depth` docstring were repaired. The proof sketch for `Language.parity_inNC_one`, however, still says that halving “gives depth `2⌈log₂ n⌉ + 2`” at lines 394-395.

At length one, the construction is a literal, so

$$
\mathrm{depth}(\mathrm{parityCircuit}\ 1)=0,
\qquad 2\lceil\log_2 1\rceil+2=2\cdot0+2=2.
$$

**Repair:** Write “gives depth at most” or explicitly put the circuit's depth on the left of an inequality. The unary-family ledger now correctly says “at most 2”; `UnaryLanguages.lean:213` could use the same wording for consistency, although the class predicate itself unambiguously specifies an upper bound.

### R2-5. MINOR — lack of a general basis guarantee is overstated as impossibility

**Round-1 connection:** residual wording introduced in the repair of finding 1; related rationale endorsed as already accurate in that resolution.

**Locations:** `FeedForward.lean:289-292`; `TCSlib/ComputationalModels.lean:73-75`; `Hierarchy.lean:47-50`; `audits/ch6-circuits-resolutions.md:17`.

The new wording says the wrapper can “never discharge an `OnlyUsesGates` obligation”; the catalog says “never a gate basis.” The valid statement is that the wrapper supplies **no general basis guarantee**. After the Boolean alphabet transport already needed to compare with `stdGateOps`, some individual wrapped gates are standard.

For example, with `C = .lit ⟨0, true⟩ : Circuit 1`, the sole wrapped gate transports to

$$
\langle\mathrm{Fin}\ 1,\ \boldsymbol{x}\mapsto x(0)\rangle
=\mathrm{andGateOp}\ 1\in\mathrm{stdGateOps}.
$$

There are no later non-input layers in this example. This is a semantic counterexample to “never,” not a claim that the repository already implements the alphabet-transport bridge.

The endorsed explanation at `Hierarchy.lean:49-50` is also too strong: an image-size expression need not explicitly mention source size to imply a useful size bound. From the tree constructors,

$$
C.\mathrm{depth}\le C.\mathrm{size}.
$$

Indeed, a literal has $0\le1$; at a node, the induction hypothesis gives

$$
1+\max_i C_i.\mathrm{depth}
\le1+\sum_i C_i.\mathrm{size}
=C.\mathrm{size},
$$

with both empty-list aggregates equal to zero. Consequently,

$$
C.\mathrm{toFeedForward.size}
=C.\mathrm{depth}+1
\le C.\mathrm{size}+1.
$$

The absent general standard-basis guarantee is sufficient to explain why this wrapper does not establish the desired class inclusion. The syntactic shape of its size expression is not an obstruction to size transfer.

**Repair:** Say “does not in general preserve the standard basis and does not supply the basis proof needed for a general simulation.” Remove the alleged impossibility based on image-size syntax from `Hierarchy.lean`. Retain the warning against using this wrapper as a general machine-to-standard-circuit construction.

### R2-6. MINOR — the replacement sweep attestation has inconsistent counts

**Round-1 connection:** finding 11's old count is corrected, but the new verification record is not reconciled.

**Locations:** `audits/ch6-circuits-reaudit-pack.md:24-27`; `audits/ch6-circuits-resolutions.md:45-53`; `scripts/circuit_module_order.txt:1-22`.

The attached list has exactly **22 nonblank, distinct entries**, confirming the acknowledged 23-versus-22 erratum. But the new pack says 22 circuit-list modules, 31 reverse dependencies, and the catalog amount to 55 modules:

$$
22+31+1=54\ne55.
$$

Overlap could only reduce the number of distinct modules. Separately, the resolutions file calls a **39-module** sweep the verification of record and says it was rerun after these repairs. Distinct sweeps could explain 39 versus the larger total, but the packet provides neither run identifiers nor module lists/log references that establish that distinction.

**Repair:** Identify the actual sweeps, their commits and module manifests/logs; correct the total or name the omitted module. State explicitly whether the 39-module sweep and the larger sweep are different runs. Record any correction to an immutable sent pack as an erratum. This does not reopen proof correctness or require an auditor-side Lean rebuild.

## 2. Disposition of every round-1 repair

“Discharged” approves the requested prose repair, not a newly implemented model bridge.

| Round-1 item | Result | Verification |
|---|---|---|
| 1 — semantic wrapper | **Partial; major remains** | Correct descriptions at `FeedForward.lean:17-22,280-293` and catalog `:73-76`; contrary overview remains at `FeedForward.lean:131-134`. See R2-1 and R2-5. |
| 2 — normal forms and metrics | **Discharged** | `Basic.lean:48-70,340-343` describes alternating trees, unequal literal paths, and separate metrics. Constructors and measures at `:349-418,660-668` match. A two-literal clause has normal-form size/depth `(1,0)` and converted size/depth `(3,1)`; empty node/clause depth differs as disclosed. |
| 3 — fixed `SIZE(T)` | **Partial; major remains** | `PPoly.lean:38-44`, `Hierarchy.lean:42-44`, and facade `:66-68` are corrected. `Hierarchy.lean:34-36` and `PPoly.lean:46-47` retain the contrary claims. See R2-2. |
| 4 — hard-function comparison | **Partial; major remains** | `HardFunctions.lean:35-53` supplies the corrected arithmetic, and facade `:54-56` says tree analogue. The old strength claim survives at `HardFunctions.lean:61-62`. See R2-3. |
| 5 — graph/nullary conventions | **Discharged** | `PPoly.lean:53-58` records unused nodes/inputs, repeated wires, nullary true and NOT-derived false; `Basic.lean:61-65` gives the empty-tree conventions; `UnaryLanguages.lean:31-34` fixes the constant-operation wording; catalog `:39-42` makes the basis restriction optional on the raw carrier. |
| 6 — missing implementations | **Discharged at the repaired Tseitin/encoding sites** | `CircuitSat.lean:41-53` says unimplemented, not impossible; `Encoding.lean:43-60` allows preorder numbering and correctly qualifies encoding inflation. The separate hierarchy size rationale is R2-5. A future full node-index type must include input variables as well as non-input gate variables. |
| 7 — machine model and `P` | **Discharged** | `CircuitSat.lean:30-39`, `Encoding.lean:34-41`, and facade `:43-46` consistently identify missing connecting theorems, rather than absent machine/class definitions. The facade also names the computability-framework bridge. |
| 8 — bounds versus equalities | **Partial; minor remains** | Unary ledger `:43-45` and parity ledger/docstring `:32-34,217` are corrected; parity's final proof sketch is not. See R2-4. |
| 9 — union equality | **Discharged** | `NCAC.lean:520-522` explicitly says the unions coincide and does not assert levelwise equality. |
| 10 — item mappings | **Discharged** | `Hierarchy.lean:312-313` attributes length three to the local count; `Universal.lean:55-56` says Exercise 6.1; resolutions `:41-44` records the section-number and item-range errata. |
| 11 — sweep-list count | **Original erratum confirmed; replacement attestation needs correction** | There are 22 list entries and the resolutions acknowledge the stale count. R2-6 records the new arithmetic and provenance discrepancy. |

For item 5, repeated AND inputs can be deduplicated by idempotence, and irrelevant non-input nodes can be discarded. Restoring every graph convention of the book can require additional wiring for unused input vertices and changed resource accounting. The repaired ledger appropriately does not promise exact size/depth preservation.

## 3. Re-issued book-item verdicts

The published 2009 numbering was rechecked. These verdicts concern each formal item together with its explicit ledger. The now-declared model differences can be accepted while inconsistent surrounding claims still keep a repair open.

| Book item | Baseline and actual Lean meaning | Round-2 verdict |
|---|---|---|
| Definition 6.1, p.107 | Book: a finite DAG, one input source per variable, one sink, binary AND/OR, unary NOT, and vertex-count size. Local: finite guarded Boolean `FeedForward` families, layering, unbounded AND, non-input size, and the graph/nullary conventions now recorded. `FeedForward.lean:43-58,94-117`; `PPoly.lean:38-58,81-85`. | **faithful-with-declared-divergence**, upgraded from divergent-undeclared. This approves the disclosed specialization, not raw unrestricted `FeedForward` as the book's carrier. |
| Definition 6.2, p.108 | Book: one circuit family recognizes the language exactly, with size at most the prescribed budget at every length. `InSIZE` has those quantifiers and recognition semantics, but uses the different metric/model now expressly disclosed. `PPoly.lean:38-44,91-123`. | **faithful-with-declared-divergence**, upgraded for the definition and ledger. The fixed classes are not identified; the surviving cross-module identification remains major R2-2. |
| Theorem 6.21, p.115 | Book: for each $n>1$, some Boolean function has no circuit of size at most $2^n/(10n)$. Local: all natural arities, tree circuits, and cutoff $\lfloor2^n/(n+5)\rfloor$. `HardFunctions.lean:252-275`; the small-arity cases remain vacuous as declared. | **faithful-with-declared-divergence**, retained as a tree-counting analogue. The verdict does not validate the contradictory strength comparison in R2-3. |

The remaining settled verdicts are unchanged. In particular, neither a proof of the book's DAG hierarchy nor a new equivalence between the tree and DAG classes is required by this verification round.

## 4. Advisory recordings and acknowledged errata

All four advisory subjects are present in the supplied resolutions excerpt, with no new implementation obligation:

| Round-1 note | Recording checked |
|---|---|
| 12 — `P` to guarded `P/poly` | Resolutions `:32-33` records gate-by-gate construction against `OnlyUsesGates stdGateOps`. The original note's evaluation, finiteness, size and finite-length contracts remain the detailed guidance; a tagged gate syntax was a suggestion. |
| 13 — CKT-SAT interface | Resolutions `:33-34` records the audited `Std.Sat.CNF ℕ` source, total string map and fixed rejecting word. This preserves the distinction between the campaign and legacy carriers and avoids assuming polynomial DAG unrolling. |
| 14 — bit-length accounting | Resolutions `:35` records dense renumbering before unary indices. `Encoding.lean:54-60` now explicitly restricts the polynomial-inflation claim to an already polynomially bounded index range. |
| 15 — computability interface | Resolutions `:36` records campaign decidability to `ComputablePred`; facade `:43-46` independently names this bridge alongside `P ⊆ P/poly`. |

**Evidence limit:** `backlog.md` itself is not an attachment. The above confirms the supplied resolutions excerpt and its statement of recording; it is not an independent inspection of the repository's backlog. This matches the packet's excerpt-based task and is not an additional gate condition.

The source-map erratum is acknowledged correctly: published Theorem 6.22 is in §6.6, and the quoted item ranges are not lists consisting solely of definitions. The original sweep-list erratum is also acknowledged correctly: 22 entries, not 23. The explanation involving commit `193470a3` is an unverified historical attestation; the separate round-2 count error is R2-6.

## 5. Closure and source record

The gate cannot close because R2-1, R2-2 and R2-3 retain the three corresponding round-1 major defects. Finishing their prose propagation, and checking the resolutions record against the resulting source, is sufficient in principle; stronger Lean theorems are not being requested. R2-4 through R2-6 are minor corrections. The four original advisory notes remain deferred guidance.

External sources rechecked, limited to attribution and model conventions:

- **AB09:** Sanjeev Arora and Boaz Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009. Definitions 6.1-6.2, Theorem 6.21, and the section heading around Theorem 6.22 in the [published-book scan](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora,_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press%282009%29.pdf), printed pp.107-108 and 115-116. The published edition, not the differently numbered Princeton draft, controls these references.
- **OD14:** Ryan O'Donnell, *Analysis of Boolean Functions*, Definitions 4.26-4.27, printed pp.103-104, in the [author's corrected edition posted in 2021](https://arxiv.org/pdf/2105.10386). The alternating-tree repair was checked against the layered carrier and internal-layer metric described there.

The numerical checks, list count, literal counterexample, and size/depth deductions above are independent semantic checks of the supplied material. They do not constitute a Lean rebuild or a new proof audit.

**Notation glossary:** $n$: input length; $C$: a circuit; $C_i$: its child circuits; $\boldsymbol{x}$ (coordinates written $x(i)$): an input assignment; $S$: tree-size budget in the quoted conversion; $T$: a size-budget function; $|C|$: the book's vertex-count size; `size` and `depth`: the indicated local carrier's measures; $\lfloor\cdot\rfloor$, $\lceil\cdot\rceil$: floor and ceiling; $\log_2$: base-two logarithm. R2-1 through R2-6 identify this report's findings; unprefixed finding/note numbers refer to round 1.

## ===== audits/ch6-circuits-resolutions.md =====

# Chapter-6 circuit surface — audit loop resolutions (OPEN, round 3 pending)

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

* **`BoolCircuit.Circuit.toFeedForward`** (tree → semantic wrapper): packages the
  tree's *evaluation* as a single unrestricted layer-0 gate `⟨Fin n, C.eval⟩`
  followed by `C.depth` identity layers, so `size = depth = C.depth + 1`.  No
  source gate is copied, no branch is padded, and no gate basis is preserved in
  general — see the declaration's docstring.
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
    general **not** in `stdGateOps`, so this map supplies **no general basis
    guarantee** and cannot serve as a general machine-to-standard-circuit
    construction — a future bridge must build its family gate by gate instead.
    (Individual wrapped gates may happen to be standard: a single positive
    literal transports to `andGateOp 1`.)  Only evaluation is preserved
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

/-- The wrapped feedforward circuit evaluates identically to the original `Circuit`.
    Proof: evalNode traces backward through identity gates at layers 1..depth, then
    the layer-0 C.eval gate computes C.eval xs from the input layer. -/
theorem Circuit.toFeedForward_eval (C : Circuit n) (x : Fin n → Bool) :
    C.toFeedForward.eval₁ x = C.eval x := by
  convert Circuit.toFeedForward_evalNode_const C x ( C.toFeedForward.depth ) ( by simp +decide [ Circuit.toFeedForward ] ) ( by simp +decide [ Circuit.toFeedForward ] ) _

/-- The wrapper prepends one evaluation layer and keeps one identity layer per
source depth unit, so depth is `C.depth + 1`. -/
theorem Circuit.toFeedForward_depth (C : Circuit n) :
    C.toFeedForward.depth = C.depth + 1 := rfl

/-
The wrapped feedforward circuit has size ≤ C.size * (C.depth + 1).
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
here, and the conversion gives no transfer in the other direction at these cutoffs
(sharing can make a DAG smaller than every tree for the same function, and only
a depth-exponential unrolling runs DAG-to-tree).  AB's theorem
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
`log S ≈ n`, against AB's generous constant `9`. That larger constant is **not** a strengthening of AB — and, per the
comparison above, nor is it a weakening: it is a tree-counting analogue with a
different cutoff in a different model, and the displayed conversion establishes
neither implication between the two stated bounds. `n + 3` would close for
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
  tree-model analogue of [AB09, Thm 6.22] and **not** that theorem, which lives in
  the book's bounded-fan-in, input-counting DAG size classes — locally only
  *rendered*, with declared divergences, by `Language.InSIZE` (see `PPoly.lean`'s
  ledger).
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
above the input is `Unit`, so its size is `C.depth + 1` whatever `C.size` is.  Size is not
the obstruction (`C.depth ≤ C.size`, so the image has size `≤ C.size + 1`): what the map
lacks is any general `stdGateOps` basis proof, which a size-class transport would need.
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
gates) and which is AB's own convention for `AC` (Def 6.25) — for *polynomial-size
existence* the fan-in choice is immaterial (budgets change by the `f - 1` factor);
exact size budgets do feel it, which is part of why fixed `SIZE(T)` is not
preserved (above).  `P/poly` imposes no depth restriction. AB's basis is `{∧, ∨, ¬}`;
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
at most `2⌈log₂ n⌉ + 2 ≤ 4(log₂ n + 1)` and fan-in `2`; polynomial size then follows from
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

/-- A unary language is decided by circuits of size at most `2`.  [AB09, Claim 6.8] -/
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
  evaluation is preserved, with no general gate-basis guarantee
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

## ===== audits/logs/ch6-baseline-sweep-premerge-state.log =====

=== TCSlib/Complexity/NPReductions/SATTo3SAT (17:38:42)
=== TCSlib/Complexity/CircuitComplexity/Basic (17:38:54)
=== TCSlib/Complexity/CircuitComplexity/Formulas (17:38:57)
=== TCSlib/Complexity/CircuitComplexity/DecisionTree (17:38:57)
=== TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit (17:39:03)
=== TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates (17:39:06)
=== TCSlib/Complexity/CircuitComplexity/PPoly (17:39:09)
=== TCSlib/Complexity/CircuitComplexity/SizeClasses (17:39:11)
=== TCSlib/Complexity/CircuitComplexity/UnaryLanguages (17:39:12)
=== TCSlib/Complexity/CircuitComplexity/UHalt (17:39:13)
=== TCSlib/Complexity/CircuitComplexity/CircuitSat (17:39:15)
=== TCSlib/Complexity/CircuitComplexity/Encoding (17:39:16)
=== TCSlib/Complexity/CircuitComplexity/Universal (17:39:17)
=== TCSlib/Complexity/CircuitComplexity/HardFunctions (17:39:19)
=== TCSlib/Complexity/CircuitComplexity/Hierarchy (17:39:20)
=== TCSlib/Complexity/CircuitComplexity/NCAC (17:39:21)
=== TCSlib/Complexity/CircuitComplexity/Parity (17:39:23)
=== TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree (17:39:44)
=== TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitSize (17:39:54)
=== TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra (17:39:56)
=== TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction (17:40:00)
=== TCSlib/BooleanAnalysis/RazborovSmolensky (17:40:03)
=== TCSlib/Complexity/CircuitComplexity (17:40:07)
BASELINE SWEEP: ALL PASS

## ===== audits/logs/ch6-batch-sweep-39mod-193470a3.log =====

=== TCSlib/BooleanAnalysis/DecisionTree (19:06:20)
=== TCSlib/BooleanAnalysis/Switching/Restriction (19:06:24)
=== TCSlib/BooleanAnalysis/Switching/BernoulliRestriction (19:06:26)
=== TCSlib/BooleanAnalysis/LMN/RestrictionCompose (19:06:28)
=== TCSlib/BooleanAnalysis/Switching/CanonicalDTree (19:06:31)
=== TCSlib/BooleanAnalysis/Switching/Encoding (19:06:37)
=== TCSlib/BooleanAnalysis/Switching/EncodingProperties (19:06:39)
=== TCSlib/BooleanAnalysis/Switching/RoundTrip (19:06:48)
=== TCSlib/BooleanAnalysis/Switching (19:06:53)
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
=== TCSlib/BooleanAnalysis/LMN/BernoulliCost (19:07:04)
=== TCSlib/BooleanAnalysis/LMN/SwitchingBernoulli (19:07:13)
=== TCSlib/BooleanAnalysis/LMN/GateSwitching (19:07:16)
=== TCSlib/BooleanAnalysis/LMN/CircuitCompression (19:07:19)
TCSlib/BooleanAnalysis/LMN/CircuitCompression.lean:246:8: warning: declaration uses 'sorry'
=== TCSlib/BooleanAnalysis/LMN/IterativeReduction (19:07:22)
TCSlib/BooleanAnalysis/LMN/IterativeReduction.lean:214:8: warning: declaration uses 'sorry'
=== TCSlib/BooleanAnalysis/LMN/NormalFormConversion (19:07:24)
=== TCSlib/BooleanAnalysis/LMN/CircuitHelpers (19:07:26)
=== TCSlib/BooleanAnalysis/LMN/RestrictionMonotonicity (19:07:44)
=== TCSlib/BooleanAnalysis/LMN/RecursiveReduction (19:07:46)
=== TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction (19:07:49)
=== TCSlib/BooleanAnalysis/LMN/Depth3Switching (19:08:06)
TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean:189:6: warning: declaration uses 'sorry'
TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean:277:8: warning: declaration uses 'sorry'
=== TCSlib/BooleanAnalysis/LMN/CompressionStep (19:08:09)
=== TCSlib/BooleanAnalysis/LMN/CircuitReindex (19:08:12)
=== TCSlib/BooleanAnalysis/LMN/GateMerge (19:08:13)
=== TCSlib/BooleanAnalysis/LMN/CircuitTreeManip (19:08:14)
TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean:379:6: warning: declaration uses 'sorry'
=== TCSlib/BooleanAnalysis/LMN (19:08:19)
=== TCSlib/BooleanAnalysis/Basic (19:08:21)
=== TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier (19:08:24)
=== TCSlib/BooleanAnalysis/LMN/RestrictionFourier (19:08:26)
=== TCSlib/BooleanAnalysis/LMN/RestrictionCardTail (19:08:29)
=== TCSlib/BooleanAnalysis/LMN/FourierConcentration (19:08:31)
=== TCSlib/BooleanAnalysis/LMN/LMNConcentration (19:08:34)
=== TCSlib/BooleanAnalysis/LMN/LayerReductionHelpers (19:08:36)
=== TCSlib/Complexity/CircuitComplexity/SizeClasses (19:08:38)
=== TCSlib/Complexity/CircuitComplexity/UnaryLanguages (19:08:39)
=== TCSlib/Complexity/CircuitComplexity/UHalt (19:08:41)
=== TCSlib/Complexity/CircuitComplexity/NCAC (19:08:42)
=== TCSlib/Complexity/CircuitComplexity/Parity (19:08:44)
=== TCSlib/Complexity/CircuitComplexity (19:09:04)
=== TCSlib/ComputationalModels (19:09:06)
BATCH SWEEP: ALL PASS

## ===== audits/logs/ch6-repair-sweep-55mod-12ff3add.log =====

=== TCSlib/Complexity/NPReductions/SATTo3SAT (10:29:40)
=== TCSlib/Complexity/CircuitComplexity/Basic (10:29:49)
=== TCSlib/Complexity/CircuitComplexity/Formulas (10:29:52)
=== TCSlib/Complexity/CircuitComplexity/FeedForward (10:29:52)
=== TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates (10:29:55)
=== TCSlib/Complexity/CircuitComplexity/PPoly (10:29:59)
=== TCSlib/Complexity/CircuitComplexity/SizeClasses (10:30:00)
=== TCSlib/Complexity/CircuitComplexity/UnaryLanguages (10:30:01)
=== TCSlib/Complexity/CircuitComplexity/UHalt (10:30:02)
=== TCSlib/Complexity/CircuitComplexity/CircuitSat (10:30:04)
=== TCSlib/Complexity/CircuitComplexity/Encoding (10:30:05)
=== TCSlib/Complexity/CircuitComplexity/Universal (10:30:06)
=== TCSlib/Complexity/CircuitComplexity/HardFunctions (10:30:07)
=== TCSlib/Complexity/CircuitComplexity/Hierarchy (10:30:09)
=== TCSlib/Complexity/CircuitComplexity/NCAC (10:30:10)
=== TCSlib/Complexity/CircuitComplexity/Parity (10:30:11)
=== TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree (10:30:32)
=== TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitSize (10:30:41)
=== TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra (10:30:43)
=== TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction (10:30:47)
=== TCSlib/BooleanAnalysis/RazborovSmolensky (10:30:51)
=== TCSlib/Complexity/CircuitComplexity (10:30:55)
=== TCSlib/BooleanAnalysis/DecisionTree (10:30:56)
=== TCSlib/BooleanAnalysis/Switching/Restriction (10:30:58)
=== TCSlib/BooleanAnalysis/Switching/BernoulliRestriction (10:31:00)
=== TCSlib/BooleanAnalysis/LMN/RestrictionCompose (10:31:02)
=== TCSlib/BooleanAnalysis/Switching/CanonicalDTree (10:31:05)
=== TCSlib/BooleanAnalysis/Switching/Encoding (10:31:11)
=== TCSlib/BooleanAnalysis/Switching/EncodingProperties (10:31:13)
=== TCSlib/BooleanAnalysis/Switching/RoundTrip (10:31:21)
=== TCSlib/BooleanAnalysis/Switching (10:31:27)
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
=== TCSlib/BooleanAnalysis/LMN/BernoulliCost (10:31:37)
=== TCSlib/BooleanAnalysis/LMN/SwitchingBernoulli (10:31:44)
=== TCSlib/BooleanAnalysis/LMN/GateSwitching (10:31:48)
=== TCSlib/BooleanAnalysis/LMN/CircuitCompression (10:31:50)
TCSlib/BooleanAnalysis/LMN/CircuitCompression.lean:246:8: warning: declaration uses 'sorry'
=== TCSlib/BooleanAnalysis/LMN/IterativeReduction (10:31:53)
TCSlib/BooleanAnalysis/LMN/IterativeReduction.lean:214:8: warning: declaration uses 'sorry'
=== TCSlib/BooleanAnalysis/LMN/NormalFormConversion (10:31:55)
=== TCSlib/BooleanAnalysis/LMN/CircuitHelpers (10:31:57)
=== TCSlib/BooleanAnalysis/LMN/RestrictionMonotonicity (10:32:14)
=== TCSlib/BooleanAnalysis/LMN/RecursiveReduction (10:32:16)
=== TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction (10:32:20)
=== TCSlib/BooleanAnalysis/LMN/Depth3Switching (10:32:35)
TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean:189:6: warning: declaration uses 'sorry'
TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean:277:8: warning: declaration uses 'sorry'
=== TCSlib/BooleanAnalysis/LMN/CompressionStep (10:32:38)
=== TCSlib/BooleanAnalysis/LMN/CircuitReindex (10:32:41)
=== TCSlib/BooleanAnalysis/LMN/GateMerge (10:32:42)
=== TCSlib/BooleanAnalysis/LMN/CircuitTreeManip (10:32:43)
TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean:379:6: warning: declaration uses 'sorry'
=== TCSlib/BooleanAnalysis/LMN (10:32:48)
=== TCSlib/BooleanAnalysis/Basic (10:32:50)
=== TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier (10:32:53)
=== TCSlib/BooleanAnalysis/LMN/RestrictionFourier (10:32:55)
=== TCSlib/BooleanAnalysis/LMN/RestrictionCardTail (10:32:58)
=== TCSlib/BooleanAnalysis/LMN/FourierConcentration (10:33:00)
=== TCSlib/BooleanAnalysis/LMN/LMNConcentration (10:33:02)
=== TCSlib/BooleanAnalysis/LMN/LayerReductionHelpers (10:33:04)
=== TCSlib/ComputationalModels (10:33:06)
REPAIR SWEEP: ALL PASS

## ===== audits/logs/ch6-round3-sweep-20mod.log =====

=== TCSlib/Complexity/CircuitComplexity/FeedForward (14:15:43)
=== TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates (14:15:51)
=== TCSlib/Complexity/CircuitComplexity/PPoly (14:15:55)
=== TCSlib/Complexity/CircuitComplexity/SizeClasses (14:15:56)
=== TCSlib/Complexity/CircuitComplexity/UnaryLanguages (14:15:57)
=== TCSlib/Complexity/CircuitComplexity/UHalt (14:15:58)
=== TCSlib/Complexity/CircuitComplexity/CircuitSat (14:15:59)
=== TCSlib/Complexity/CircuitComplexity/Encoding (14:16:01)
=== TCSlib/Complexity/CircuitComplexity/Universal (14:16:02)
=== TCSlib/Complexity/CircuitComplexity/HardFunctions (14:16:03)
=== TCSlib/Complexity/CircuitComplexity/Hierarchy (14:16:04)
=== TCSlib/Complexity/CircuitComplexity/NCAC (14:16:05)
=== TCSlib/Complexity/CircuitComplexity/Parity (14:16:07)
=== TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree (14:16:26)
=== TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitSize (14:16:35)
=== TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra (14:16:37)
=== TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction (14:16:40)
=== TCSlib/BooleanAnalysis/RazborovSmolensky (14:16:44)
=== TCSlib/Complexity/CircuitComplexity (14:16:48)
=== TCSlib/ComputationalModels (14:16:49)
ROUND3 SWEEP: ALL PASS

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

## ===== scripts/switching_module_order.txt =====

TCSlib/Complexity/CircuitComplexity/Basic
TCSlib/Complexity/CircuitComplexity/Formulas
TCSlib/BooleanAnalysis/DecisionTree
TCSlib/BooleanAnalysis/Switching/Restriction
TCSlib/BooleanAnalysis/Switching/BernoulliRestriction
TCSlib/BooleanAnalysis/LMN/RestrictionCompose
TCSlib/BooleanAnalysis/Switching/CanonicalDTree
TCSlib/BooleanAnalysis/Switching/Encoding
TCSlib/BooleanAnalysis/Switching/EncodingProperties
TCSlib/BooleanAnalysis/Switching/RoundTrip
TCSlib/BooleanAnalysis/Switching
TCSlib/BooleanAnalysis/LMN/BernoulliCost
TCSlib/BooleanAnalysis/LMN/SwitchingBernoulli
TCSlib/BooleanAnalysis/LMN/GateSwitching
TCSlib/BooleanAnalysis/LMN/CircuitCompression
TCSlib/BooleanAnalysis/LMN/IterativeReduction
TCSlib/BooleanAnalysis/LMN/NormalFormConversion
TCSlib/BooleanAnalysis/LMN/CircuitHelpers
TCSlib/BooleanAnalysis/LMN/RestrictionMonotonicity
TCSlib/BooleanAnalysis/LMN/RecursiveReduction
TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction
TCSlib/BooleanAnalysis/LMN/Depth3Switching
TCSlib/BooleanAnalysis/LMN/CompressionStep
TCSlib/BooleanAnalysis/LMN/CircuitReindex
TCSlib/BooleanAnalysis/LMN/GateMerge
TCSlib/BooleanAnalysis/LMN/CircuitTreeManip
TCSlib/BooleanAnalysis/LMN
TCSlib/BooleanAnalysis/Basic
TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier
TCSlib/BooleanAnalysis/LMN/RestrictionFourier
TCSlib/BooleanAnalysis/LMN/RestrictionCardTail
TCSlib/BooleanAnalysis/LMN/FourierConcentration
TCSlib/BooleanAnalysis/LMN/LMNConcentration
TCSlib/BooleanAnalysis/LMN/LayerReductionHelpers
