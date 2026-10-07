# Chapter 6 circuit surface: round-3 closing verification

**Disposition: the gate closes under the specified zero-blocker/major rule.** This round finds **0 blockers, 0 majors, 2 minors, and 0 new advisory notes**. The three round-2 major semantic defects are discharged in the supplied Lean source. R2-4 is discharged. R2-5 and R2-6 are partially discharged: one unqualified basis claim survives, and the attached resolutions record lacks the promised appendix and errata. Gate closure therefore does **not** mean that all six repairs are complete.

Audited input: `ch6-circuits-round3-bundle.md`, presented as repair commit `3ff0d76b` on `complexity/arora-barak-ch1`. Audit date: 2026-10-02.

Bundle SHA-256: `c5572c6bcc68edf5778489ab5e4a0f971028cf334b298dfdfbd10a0097457f34`.

The bundle contains 15 attachment sections: the round-2 findings, the resolutions record, six circuit Lean files, the computational-model catalog, four logs, and two order lists. This was a single-agent, packet-evidence verification. No input source was modified, no Lean rebuild was performed, and settled proof/attack results were not reopened.

References to `FeedForward.lean`, `Hierarchy.lean`, and the other circuit filenames abbreviate `TCSlib/Complexity/CircuitComplexity/`. Source line 1 is the first line after an attachment header and its separating blank line. “Opening pack” references use the original bundle's lines 1–63.

## 1. Findings

### R3-1. MINOR — the promised updated resolutions, verification appendix, and errata are absent

**Locations:** opening pack `:10-15,34-40,55-60`; `audits/ch6-circuits-resolutions.md:17,45-61`; `audits/logs/ch6-batch-sweep-39mod-193470a3.log:1-51`.

The opening pack says the attached resolutions file itemizes the six repairs, contains errata R-E1/R-E2, and has an appendix identifying runs A–D. The actual attachment is only **61 lines** long. It ends after the round-2 task brief; there is no R2-1…R2-6 disposition table, verification appendix, R-E1 text, or R-E2 text. This is also visible directly at bundle lines 356–364, where the round-2 brief is immediately followed by the `FeedForward.lean` attachment.

Two unreconciled passages remain:

- Line 17 retains “never discharges `OnlyUsesGates`,” the historical assertion that the false size bound was removed in round 1, and the endorsement of `Hierarchy.lean` as already accurate and untouched. The first statement is the R2-5 overstatement; the latter two need the historical correction promised as R-E1. The current source does remove the false bound, but that does not correct the recorded history.
- Lines 50–53 still describe the 39-module sweep as covering the current 22-entry circuit list plus the Switching/LMN reverse dependencies and catalog, “re-run after this round's repairs.” The supplied 39-module log instead has **32 Switching/LMN-side entries, six circuit-list entries, and the catalog**. It does not list all 22 circuit modules: for example, `FeedForward`, `PPoly`, `HardFunctions`, and `Hierarchy` are absent as explicit compilation entries. It cannot stand as the module manifest claimed by that sentence.

The raw logs resolve the numerical ambiguity independently: the 39- and 55-module sweeps are different sequences, and the corrected 55-module arithmetic is right. However, reconstructing that reconciliation here does not make the promised appendix or errata present in the packet. The logs contain times of day, but no embedded commit attestations or commands; their filenames and the opening pack supply the available state associations.

**Required repair:** Supply the updated resolutions record. Record R2-1…R2-6 individually; add R-E1 correcting the round-1 removal/endorsement claims and the categorical basis wording; add R-E2 identifying the immutable round-2 pack's `31` as `32`, with `22 + 32 + 1 = 55`. Replace the stale 39-module sentence with an appendix distinguishing the four runs, their actual module sequences, their asserted source states, and their log paths. Preserve the sent packs and prior findings unchanged. The reconstruction in §3 below provides the independently checked counts.

**Severity rationale:** This continues the audit-record/provenance issue already classified as minor in R2-6, with stale R2-5 wording in the same record. The supplied source repairs and log arithmetic do not reveal a new major semantic defect or a failed Lean proof. I cannot claim to have reviewed two errata texts that are absent.

### R3-2. MINOR — the hierarchy ledger still asserts categorical basis non-membership

**Locations:** `Hierarchy.lean:48-53`; compare `FeedForward.lean:286-296` and `TCSlib/ComputationalModels.lean:73-76`.

The hierarchy paragraph still describes the wrapped operation as a gate “that is not in `stdGateOps`.” Its new concluding sentence correctly says that a **general** basis proof is absent, but the earlier clause remains unqualified. The declaration docstring and catalog now use the correct generality qualification.

The same explicit counterexample from R2-5 applies. Take

\[
C:=\mathrm{Circuit.lit}\langle0,\mathrm{true}\rangle:\mathrm{Circuit}\ 1.
\]

Then `C.depth = 0`, `C.eval` is the sole input projection, and the wrapper has exactly one non-input gate and no subsequent identity layers. After the Boolean-to-`Fin 2` alphabet identification, its operation is

\[
\left\langle\mathrm{Fin}\ 1,\ \boldsymbol{x}\mapsto x(0)\right\rangle
=\left\langle\mathrm{Fin}\ 1,\ \boldsymbol{x}\mapsto
\prod_{i\in\mathrm{Fin}\ 1}x(i)\right\rangle
\in\mathrm{stdGateOps},
\]

by the `n = 1` member of the union in `FeedForward.lean:114-117`. This is a semantic counterexample after alphabet identification, not a claim that a transport bridge has been implemented in Lean. Comparing the untransported `Bool` operation directly with a set of `Fin 2` operations is not a well-typed membership statement.

**Required repair:** Replace the clause with “an unrestricted gate that, even after alphabet transport, need not belong to `stdGateOps`.” Keep the corrected size bound and the statement that there is no general basis guarantee. For precision, the positive-literal example at `FeedForward.lean:294-295` can explicitly specify `C : Circuit 1`, as the counterexample does.

**Severity rationale:** This is the remaining local overstatement from minor R2-5. It does not undo the semantic-wrapper repair or assert a valid general circuit simulation.

## 2. Disposition of R2-1…R2-6

| Finding | Verdict | Verification against the supplied source |
|---|---|---|
| **R2-1 — structural embedding** | **Major semantic defect discharged; record correction incomplete** | `FeedForward.lean:131-135,281-296,331-345` consistently describes a semantic wrapper: one evaluation gate, followed by `C.depth` identity layers, with size and depth `C.depth + 1`. The construction at `:297-316` matches. The false `C.size * C.depth` bound and branch-padding explanation are gone. The surviving bound at `:344-348` is the different, valid `C.size * (C.depth + 1)`. R3-1 covers the stale resolutions row. |
| **R2-2 — fixed-size identification and fan-in** | **Discharged** | `Hierarchy.lean:34-38` identifies the book's bounded-fan-in, input-counting DAG classes and explicitly qualifies the local rendering. `PPoly.lean:38-54` distinguishes fixed budgets from polynomial-size existence and expressly allows budget changes in the fan-in conversion. |
| **R2-3 — strength comparison** | **Discharged** | `HardFunctions.lean:43-55,61-66` gives a tree-counting analogue with a different cutoff, qualifies the comparison by the displayed conversion, and no longer claims that tree hardness “never” rules out small DAGs. The depth-exponential unrolling remains distinguished from an available polynomial bound. The arithmetic checks: `2^20 = 1,048,576`; `floor(1,048,576/200) = 5,242`; `5,242 - 40 = 5,202`; `floor(1,048,576/25) = 41,943`. |
| **R2-4 — depth/size bounds** | **Discharged** | `Parity.lean:394-395` now says “depth at most,” agreeing with `xorFuel_depth` and `parityCircuit_depth_le` at `:217-221,329-338`. The length-one literal is no longer a counterexample to the prose. `UnaryLanguages.lean:213` also now says “size at most 2,” consistent with `:175-180`. |
| **R2-5 — general basis guarantee and size rationale** | **Partially discharged; minor remains** | `FeedForward.lean:290-296` and catalog `:73-76` correctly disclaim a general basis guarantee. `Hierarchy.lean:51-53` correctly removes size as the obstruction and records `C.depth + 1 ≤ C.size + 1`. Its unqualified gate-membership clause remains R3-2; the stale resolutions wording is included in R3-1. |
| **R2-6 — verification record** | **Partially discharged; counts verified, record incomplete** | Both order lists and all four raw logs are supplied. Their counts, run-C disjointness, and the proposed R-E2 arithmetic check independently; see §3. The promised run appendix and actual errata texts are absent, and the old 39-module description survives: R3-1. |

“Discharged” here approves the commissioned prose repair. It does not assert a newly implemented model bridge or an independently verified documentation-only Git diff.

## 3. Independent reconciliation of the verification logs

The run labels below identify the four attached logs in their apparent intended A–D order. They do not supply missing historical metadata. I counted lines beginning `=== `, extracted each module path before its timestamp, checked uniqueness, and compared the ordered module sequences with the two supplied lists.

| Run | Attached log under `audits/logs/` | Distinct module entries | `error:` lines | `warning:` lines | Final marker |
|---|---|---:|---:|---:|---|
| A | `ch6-baseline-sweep-premerge-state.log:1-24` | 23 | 0 | 0 | `BASELINE SWEEP: ALL PASS` |
| B | `ch6-batch-sweep-39mod-193470a3.log:1-51` | 39 | 0 | 5 | `BATCH SWEEP: ALL PASS` |
| C | `ch6-repair-sweep-55mod-12ff3add.log:1-67` | 55 | 0 | 5 | `REPAIR SWEEP: ALL PASS` |
| D | `ch6-round3-sweep-20mod.log:1-21` | 20 | 0 | 0 | `ROUND3 SWEEP: ALL PASS` |

There are no duplicate module markers within any run.

**Order lists and run C.** `scripts/circuit_module_order.txt:1-22` contains 22 nonblank, distinct paths. `scripts/switching_module_order.txt:1-34` contains 34. The two **full** lists overlap in exactly:

- `TCSlib/Complexity/CircuitComplexity/Basic`;
- `TCSlib/Complexity/CircuitComplexity/Formulas`.

The second segment of run C omits precisely those first two Switching-list entries. Thus its count is

\[
34-2=32.
\]

More strongly, ordered equality holds: run C log lines 1–22 equal the entire circuit list; its module markers on lines 23–65 equal Switching-list lines 3–34; line 66 is `TCSlib/ComputationalModels`. Those two actual run-C segments have empty intersection, and the catalog occurs in neither. Consequently,

\[
22+32=54,\qquad54+1=55.
\]

The run-C disjointness claim is therefore correct for these segments. It would not be correct for the two full order lists. The R-E2 numerical correction is also correct: the old `22 + 31 + 1` gives 54, while replacing 31 by 32 gives the logged 55. The missing appendix does not prevent this independent arithmetic check.

**Run B.** Its first 32 module markers equal Switching-list lines 3–34. Its remaining seven markers, at log lines 44–50, are `SizeClasses`, `UnaryLanguages`, `UHalt`, `NCAC`, `Parity`, the `CircuitComplexity` facade, and the catalog. The first six are the only entries it shares with the circuit list. Therefore,

\[
32+6+1=39.
\]

This establishes that B and C are distinct sweeps; it does not establish the stale claim that B explicitly swept all 22 circuit-list modules.

**Run D.** Its first 19 markers equal circuit-list lines 4–22, starting at `FeedForward`, and its twentieth is the catalog:

\[
(22-4+1)+1=19+1=20.
\]

All six edited circuit modules and the edited catalog occur. The opening pack associates this run with the round-3 repair; the log itself does not name a commit.

**Run A.** It contains 23 distinct markers. Relative to the current circuit list, it omits the new `CircuitComplexity/FeedForward` path and adds the old `RazborovSmolensky/FeedForwardCircuit` and `CircuitComplexity/DecisionTree` paths; all other module paths match. Hence

\[
22-1+2=23.
\]

This corroborates the old/new list-count explanation at the level of supplied paths, without independently proving the asserted relocation commit or historical timing.

**Warnings and provenance.** Runs B and C each record five `declaration uses 'sorry'` warnings in the same four LMN files: `CircuitCompression`, `IterativeReduction`, `Depth3Switching` (two declarations), and `CircuitTreeManip`. Locations are B `:20,22,29-30,35` and C `:42,44,51-52,57`. These are outside the commissioned Chapter-6 circuit source surface; they do not contradict its zero-sorry attestation. “Zero `error:` lines” should not be paraphrased as “warning-free” for B or C. Both also contain the same `ring` tactic suggestion, without an `error:` diagnostic.

The supplied logs support these content/count comparisons and their printed success markers. They do not independently authenticate the commits, fresh-olean procedure, compiler/mathlib versions, complete import graph, or lint execution. In particular, an order list alone cannot prove the opening pack's claim that the Switching/LMN trees import none of the six edited files. These remain maintainer attestations, rather than new gate conditions.

## 4. Residual pass and retained verdicts

The repaired overviews, divergence ledgers, declaration comments, catalog entry, opening pack, and entire supplied resolutions record were reviewed. All nine retired phrases listed in opening-pack lines 27–31 have zero occurrences in the **seven attached Lean files**, including after whitespace normalization. The full-tree and `backlog.md` grep cannot be repeated from this packet; neither the complete tree nor the backlog is attached. R3-2 illustrates the remaining semantic overstatement outside those exact search phrases.

No additional blocker or major was found in the repaired prose. R-E1's text is unavailable for review; its promised historical correction is not implemented in the attached record. R-E2's correction is accurately summarized in the opening pack and numerically verified above, but its promised erratum text is likewise absent.

The settled **faithful-with-declared-divergence** verdicts for Definitions 6.1 and 6.2 and Theorem 6.21 stand. This round adds no claim that the raw unrestricted carrier is the book's circuit model, that the fixed size classes coincide, or that the tree-counting analogue proves the book's quantified DAG theorem. The four earlier advisory interface notes remain deferred guidance; no new implementation obligation is introduced.

Under the commissioned rule, **zero blockers and zero majors closes the gate**. The two remaining repairs are the documentary corrections specified in R3-1 and R3-2.

**Notation glossary:** `C`: the source tree circuit; `C.depth` and `C.size`: its local depth and node-count measures; `Circuit 1`: a tree circuit with one input variable; `n`: input arity; `Fin n`: the finite type of indices from 0 to `n − 1`; `Bool` and `Fin 2`: the two Boolean alphabets; `x` (boldface in the displayed operation): a gate-input assignment; `∏`: product; `stdGateOps`: the gate set defined in `FeedForward.lean:114-117`; `floor`: integer floor. A–D are the run labels used in §3; R2-1…R2-6 refer to the supplied round-2 findings, R3-1/R3-2 to this report, and R-E1/R-E2 to the promised errata.
