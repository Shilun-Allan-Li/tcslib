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
