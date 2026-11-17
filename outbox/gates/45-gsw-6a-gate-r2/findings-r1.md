# Gate 45 · round 1 findings (Codex), filed verbatim

Received from Seyoon as an upload, 2026-11-17 (`gate45-gsw-6a-findings.md`). The `audit/target-review.tsv` it cites was
not supplied.

---

# Gate 45 — GSW phase 6a, round 1

**Overall verdict: HOLD. PR #358: CLEAR. PR #359: HOLD.**

All 98 admitted targets are mathematically sound as stated and strong enough for the named r3 consumers. The hold concerns an additional, undisclosed duplication that LE-ren did not remove.

| Audited item | Pinned revision |
|---|---|
| Exchange | `059331913c8a5380d3ae53e5e9dffa3c7ff6e2b4` |
| Campaign records | `8c5875fa268a622e4e166da5f7a992715097c2c7` |
| #358 / merge base | `a616adcac0760ab56b1b0a2a4869f4763843f9ab` / `e1d39836ed4a69a34914c35f4c73c71de853dcc6` |
| #359 / stacked base | `73aedcdaaaffef7e69ab012d9b9195f150bae68d` / `a616adcac0760ab56b1b0a2a4869f4763843f9ab` |

Open findings, counted once against the PR introducing the issue:

| PR | Blockers | Majors | Minors | Notes | Verdict |
|---|---:|---:|---:|---:|---|
| #358 | 0 | 0 | 0 | 1 | **CLEAR** |
| #359 | 0 | 1 | 1 | 0 | **HOLD** |
| Overall | 0 | 1 | 1 | 1 | **HOLD** |

## Findings

Lean paths below are relative to `TCSlib/Complexity/`.

| ID | Severity | PR · location | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| **G45-01** | **Major** | #359 · `CircuitComplexity/FormulaArith/Combinators.lean:425`, `TreeCircuit.const_eval` | This admitted target exactly restates public, proved `BoolCircuit.eval_node_nil` at `CircuitComplexity/Hierarchy.lean:105`, after `const_eq`. Its sketch re-derives the identity by splitting the Boolean gate kind. Neither the overlap inventory nor DL-54 discloses or accepts this duplicate. Under policy §1 and the G44-01 precedent, a new name and a definition wrapper do not resolve exact theorem duplication. | Reuse the existing fact, moving it to an upstream shared module if necessary; make the new reader a citation and remove it from the admitted-target inventory. Alternatively, record Seyoon's explicit acceptance and a ledger row with the shared home and repayment point. Correct the overlap inventory. |
| **G45-02** | **Note** | #358 · `CircuitComplexity/FormulaArith/Combinators.lean:15` | “Promoted unchanged” accurately describes the computation, but can be read as claiming byte-identical moved proofs. There were five sound, Q2-approved repairs. #359 inherits this sentence. | Optionally clarify that the computation is unchanged and the proofs have the five approved repairs. |
| **G45-03** | **Minor** | #359 · `BranchingPrograms/Barrington.lean:40` and `:339` | The convention prose calls `(13254)` “0-based.” That is Bar89's **one-based** cycle notation; its zero-based translation is `(0 2 1 4 3)`, as the code correctly implements. | Label the notation correctly. The formal permutations and statements need no change. |

The exact equality behind G45-01 is:

```lean
TreeCircuit.const b = TreeCircuit.node b []                 -- const_eq
(TreeCircuit.node b []).eval x = b                         -- existing eval_node_nil
(TreeCircuit.const b : TreeCircuit n).eval x = b            -- new admitted const_eval
```

Importing `Hierarchy` directly into `Combinators` would create a cycle: `Hierarchy` imports `TreeNCAC`, which imports `Combinators`. This explains the need for an upstream move or explicit accepted debt; it does not establish acceptance.

## Proof, statement and source audit

| Surface | Result |
|---|---|
| **#358 move and proofs** | **Pass.** The diff is exactly four files, +279/−184. The moved block has the stated renaming/promotion, five repairs, three line re-wraps, promoted documentation and two new `rfl` readers. All seven public declarations are sound. Pairing preserves the gate's Boolean value, halves list length with ceiling, adds at most one depth level and does not increase `sumSize + length`. The fuel induction establishes the published fan-in, depth and size bounds, including the empty and singleton lists. |
| **Frozen `TreeNCAC` surface** | **Pass.** Public statements are unchanged. `toBinary` computes the same circuit after replacing private `combine` by the identical `balanced` construction. The two remaining seal failures and four explicit foreign unfolds are pre-existing G6A-F05, not introduced by O1. |
| **C1–C4: 11 targets** | **Pass.** Composition order, conjugation, last-instruction complement, lengths and bijectivity match the model. The positive-length hypothesis is necessary for the complement-yield equation. Empty programs and zero width/input arity have the expected interpretations. |
| **C5–C8: 5 targets** | **Pass.** The push form works for general maps; permutation fibers are singletons, giving C6's pull form. Prefix induction proves the indexed relational contract C7. A pushed one-hot vector remains one-hot even for noninjective maps. These contracts suffice for G2. |
| **C9–C16: 11 targets** | **Pass mathematically; G45-03 concerns cycle-label prose.** The commutator and explicit orbit-matching conjugator have the required orientation. The four-block AND construction cancels on rejection; the OR construction correctly complements both children and the result. Constants, unary gates, arbitrary output permutations in C14, and nonemptiness are handled. C13/C16 correctly require fan-in at most two and a five-cycle. |
| **C17–C21: 11 targets** | **Pass.** The instruction wires, composition formula, midpoint recursion and accepting-function enumeration implement Bar89's three proof sections. The composition bound is `(clog 2 w + 2) * clog 2 length + 1`; the acceptance constant `w * clog 2 w + clog 2 w + 3` suffices because the accepting set has at most `w^w` functions. Widths zero/one, lengths zero/one and empty accepting sets are covered. |
| **C22–C25: 5 targets** | **Pass.** `IsFaninTwo` supplies the well-formedness needed for tree unrolling. The family statements are nonuniform NC¹/BWBP/PBP₅ statements. Polynomial lengths/depths give the advertised inclusions; the accepting set handles input length zero. |
| **N1–N6: 6 targets** | **Pass.** Every gadget case satisfies all seven `GadgetSpec` fields, including empty/unary gates. Cost is at most fan-in plus two; depth factor two and size `n + 4 * #gates` follow from the existing rewrite contracts. NAND form does not imply `IsWellFormed`; those predicates can overlap on unary-only circuits. |
| **N7–N13: 7 targets** | **Pass.** The column invariant supplies in-range copies at every required level. Base copies, parity twins and double-NAND links preserve values under `IsNANDForm`; their depth and acyclicity arguments need no NAND hypothesis. The empty-gate twin uses the literal pair and needs positive input arity. Output depth is preserved exactly, including depth zero; dead columns cause no problem. N11's bound covers every column. N12 is exactly the required `args_lt` field, equivalent to the planned `GatesAcyclic` proposition, as ruled by Q4. |
| **F1–F3: 24 targets** | **Pass mathematically; G45-01 concerns reuse.** De Morgan negation preserves depth and fan-in. Substitution and finite-supremum bounds include the empty variable type. Gadget truth tables, depth increments and fan-in bounds are correct. |
| **F5–F6: 7 targets** | **Pass.** The weighted full-adder identity preserves the sum; padding and unequal/empty word lengths are correct. One layer sends `k` words to `2 * (k / 3) + k % 3`; the two-round shrinkage supports `csaLevels k ≤ 2 * clog 2 k`, including counts zero, one and two. |
| **F7–F8: 7 targets** | **Pass.** Generate/propagate gives the ripple carry, and the threshold theorem has the necessary word-length bounds. For `p = max lengths + 1`, the CSA carry word's top bit is `maj(false,false,T) = false`, so comparison works for every constant, including zero, `2^p` and larger constants. The padding-depth and `+7` bounds are sound. |
| **F9–F10: 4 targets** | **Pass.** For positive modulus the sum bound `S < max M 1 * q ≤ 2^w` justifies trimming both nonnegative words; the quotient gives the interval witness. Empty/reversed intervals, `M = 0` and `q = 1` work. If `q = 0`, the hypotheses force `M = 0` and `lo = hi = 0`, and both sides are false; that case must precede the division argument in the fill. The closed depth bound has no term linear in `log q`. |

These counts sum to **98**. `audit/target-review.tsv` records every declaration individually, with its domain/edge checks, reasoning and consumer. This is a semantic audit of admitted statements, not 98 completed Lean proofs.

**C16 reading.** BV14 accepts return to its start state. Here C16 gives `(barrington c σ).yield x 0 = σ 0` on acceptance and `0` on rejection. Since a five-cycle moves `0`, G3 must read coordinate `σ 0`; coordinate `0` would encode the complement. The deviation is mathematically harmless and is disclosed, although spelling out this acceptance distinction would make the note clearer.

**Definitions and consumers.** No definition contains a `sorry` body. The only non-target constants reaching `sorryAx` are `toNANDForm`, `toNANDForm_eq`, `layerNAND`, `layerNAND_gates` and `layerNAND_output`: two definitions and three theorems. N2 enters `rewrite` only through correctness proofs; N12–N13 enter only through structure proof fields. The gate lists and output indices do not compute from admitted witnesses. This is acceptable for the explicitly planned statement phase. The 89 self-only and nine additional target traces are exactly as disclosed. The proved readers/helpers and decidability instances are sound; the separate Q3 readers remain fill prerequisites, outside this audit.

**Reuse and registration.** LE-ren completely removes the `rename` family. `widenCircuit` is a specialization of `reidx`; `restrictCircuit` is a special case of general substitution, not a theorem that proves general substitution. No additional duplicate of those families remains. DL-54 correctly records the deferred relocation of `reidx`. The computable C10 contract is stronger than Mathlib's conjugacy-existence theorem. Other compared circuit models and private dual-rail machinery are not interchangeable public theorems. G45-01 is the additional exact public overlap. Both models, all four conversions, facades, and H18–H20 are registered correctly; the listed contract locations resolve. `Combinators` is 629 lines; the stated fill-time split condition is reasonable.

**Sources.** All 112 anchors resolve in the pinned ingests. The 18 exact and six rendering-different quotations check against their passages, including C6's pull equation. The source results, disclosed glue/deviations and reference lines are appropriate, subject to G45-03. Bar89's downloaded original matches the ingest's PDF SHA-256, and the relevant scanned theorem/lemma pages agree. BV11/BV14 comparison used the pinned ingests; independent PDF fetches were unavailable. The retained AB09 tag is pre-existing; no Gen09 issue arises.

## Replay and Rule 10 evidence

**Integrity verified:** 13/13 outer checksums; 483/483 verification-archive files; 42/42 source copies bound to git; all 86 bundle sections bound to their stated sources. The two additional raw archives verify 984/984 and 260/260 files and their pinned outer hashes. The delivery manifests verify 2137/2137 and 2105/2105 with exact file sets. All six worker commits reproduce hash-for-hash with `git am`; the 1,345 raw build logs recount cleanly. Declaration drift is **267 added / 0 changed / 0 removed** against the tip, including O1's seven declarations.

| Snapshot-#5 evidence | #358 / R1 | #359 / R2 |
|---|---:|---:|
| Successful rebuilt modules | 9/9 | 20/20 |
| Checked module states | 1429/1429 | 1440/1440 |
| Admission delta | +0 | +98, exact targets |
| Axiom census | 141 constants, standard only | 544 constants; `sorryAx` in 98 targets + five dependents |
| Canonical owner records reproduced | 4/4 | 16/16 |

Build log/source hashes, state keys and recorded object hashes agree with the pinned heads. The two snapshot-#4 landing **full trees** reconstruct exactly as `ba964762…` and `34e41f15…`. Equal-key modules also have identical recorded olean hashes: 1,413 in R1 and 1,424 in R2. The axiom logs are byte-identical between snapshots.

Exact statement-owner request counts, in **strict A / strict B / coe-A / coe-B** order:

| Owner | A | B | coe-A | coe-B | Errors per variant |
|---|---:|---:|---:|---:|---:|
| BP/Defs | 0 | 0 | 0 | 0 | 0 |
| BP/Eval | 25 | 25 | 25 | 25 | 0 |
| BP/Barrington | 119 | 119 | 119 | 119 | 0 |
| BP/BarringtonConverse | 243 | 243 | 243 | 243 | 0 |
| BP/NC1 | 333 | 333 | 333 | 333 | 0 |
| BranchingPrograms facade | 335 | 335 | 335 | 335 | 0 |
| FA/Combinators | 174 | 174 | 174 | 174 | 0 |
| FA/CarrySave | 253 | 253 | 253 | 253 | 0 |
| FA/Compare | 269 | 269 | 269 | 269 | 0 |
| FA/ModSum | 273 | 273 | 273 | 273 | 0 |
| FormulaArith facade | 276 | 276 | 276 | 276 | 0 |
| NANDForm | 180 | 180 | 180 | 180 | 0 |
| NANDLayering | 187 | 187 | 187 | 187 | 0 |
| TreeNCAC | 218 | 218 | 218 | 218 | 2, pre-existing |
| CircuitComplexity facade | 3726 | 3726 | 3726 | 3726 | 0 |
| ComputationalModels | 1106 | 1107 | 1106 | 1107 | 0 |
| **Total** | **7717** | **7718** | **7717** | **7718** | **2** |

O1's four owners have **174/194/194/3659** requests respectively in each variant (`Combinators`/`FormulaArith`/`TreeNCAC`/`CircuitComplexity`), totaling **4221**; only `TreeNCAC` has its two inherited failures. The base file has 94 requests and four failures, including the two nil cases O1 repairs.

The delivered root counts are exactly **13762/13763/13761/13762**, all clean. Phase 2 root coe-A has **13991** requests; snapshot #5 has **14074**, in 15 verified chunks with zero errors. Its 83 additions are confined to #340/#346. A/B differs by `PolyExpr.eval`; strict/coe differs by the projection `CoeFun` instance. The latter is absent from the `ComputationalModels` closure, explaining that owner's two equal pairs. These are variant counts, not interchangeable totals.

**Controls:** per harness (strict or coe), O1 has eight probes, four sealed, with **10 negative + 10 reader** checks under seals and 20 unsealed checks. The statement run has 40 probes, 20 sealed, with **92 negative + 92 reader** checks under seals and 184 unsealed checks. Every negative fails exactly once; readers and unsealed checks pass. The delivered controls independently recount **30/30**. The explicit-unfold scan has zero foreign reads in the 13 new files and precisely the four inherited `TreeNCAC` reads.

**Carry-forward argument: confirmed for the claimed checks.** I reconstructed the old trees, recomputed the closure keys, reconstructed conservative request sets from collector catalogs, recovered source bytes from the instrumented probes, and checked their hashes, install/EOF coverage and raw errors. All 20 canonical owner records match. All 26 reused tools match archived copies. The collectors import the same owner union; strict/coe-B generation and controls use fixed variant settings and those records, not the root or discovery of unrelated snapshot modules. With the fixed Mathlib/toolchain, no changed input to the carried checks was identified. The root's closure changed and its canonical seal was rerun. This confirms reuse of recorded results; it is not a claim that those variants were freshly executed on #5.

## Grades of G6A-F01–G6A-F15

These dispositions are not additional open findings.

| Review finding | Audit grade / disposition |
|---|---|
| F01 | Agree: the specific `rename` duplicate is closed by LE-ren. Reject a broader “no remaining duplication” conclusion: **G45-01**. |
| F02 | Agree: semantics-free repairs, explicitly accepted by Q2; controls cover both extra nil cases. |
| F03 | Agree: separate reader prerequisite, ruled by Q3 and out of scope here. |
| F04 | Agree: equivalent field-form N12, accepted by Q4; no mathematical defect. |
| F05 | Agree: pre-existing failures and unfolds; independently confirmed. |
| F06 | Agree: size watch, not a present blocker or major; retain the fill split trigger. |
| F07 | Agree: documentation note, **G45-02**. The computation is unchanged; qualifying the claim about the proofs would improve precision. Bibliographic spelling/abbreviation and “frozen” wording do not change source identity. |
| F08 | Agree: the 16 disclosed adaptations and settled constants preserve the intended contracts. |
| F09 | Agree: redundant `lo ≤ hi` is harmless and follows r3; no contradiction. |
| F10 | Agree: tooling/environment note; chunking has complete request coverage. |
| F11 | Agree: convention note. BV14 accepts return to its start state; C16's five-cycle recognizer accepts at `σ 0`. Reading state `0` here would give the complement. The stated deviation is sound; explicitly spelling out the acceptance change would help readers. G45-03 is a separate cycle-label defect. |
| F12 | Agree: historical freshness note, superseded by the verified #5 replay. |
| F13 | Agree: checkpoint source/head gaps are closed by final delivery and reproduction. |
| F14 | Agree: trace correction is accurate; nine targets additionally reach N2 or N12–N13. |
| F15 | Agree: process note. The terminal driver syntax error is disclosed; every required child result, source binding and seal/control record is complete. It does not invalidate the recorded checks. |

The pack's other listed slips are accounted for: old review heads, snapshot numbering, “five definitions,” record-versus-distinct-owner counts, range-diff wording and missing tool-match annotations. G45-01 is an additional undisclosed overlap. No other blocker or major was identified.

**Verification limit:** I did not run a fresh Lean compilation. Compilation, axiom and seal conclusions use the supplied, hash-bound raw runs, independently recounted and compared with the inspected source. Q3 readers, in-house fills, Gate 46, bootstrapping/circular security, Gen09, merge order and snapshot adoption remain outside the requested audit. The user dispatches and merges.

**Notation:** BP = `BranchingPrograms`; FA = `CircuitComplexity/FormulaArith`; `b` = Boolean gate kind; `c` = formula; `x` = input assignment; `n` = input arity; `σ` = five-cycle; `w` = branching width or, in the F9 discussion, retained bit count; `D` = output depth; `δ` = old vertex depth; `k` = word count; `M` = summand count; `q` = modulus; `S` = subset sum; `p` = comparison width; `U,W` = carry-save words; `lo,hi` = interval endpoints; `T` = a bit of the added constant. Campaign labels retain the pack's meanings.
