Input SHA-256: `28b7f2c805088d35209cb67a1c652d2e8d7087b4bbba2a360dd5216df9354191` — matches the expected digest.

Section count: **exactly 82** headers of the form `## ===== <path> =====`.

# Stage 2 statement-gate audit

Audit date: 2026-10-14. Scope: the three proposed units in `audits/evidence/stage2-gate/`, their supporting definitions, and every question and attestation in `audits/stage2-statements-pack.md`.

**Verdict: the statement gate meets its stated closure criterion: zero blockers and zero majors. There are four minor findings.** I found no false proposed theorem. This verdict concerns the mathematical statements and specification mirror; it does not certify completed proofs, the future PROG-2 compiler edit, or an independently reproduced Lean build.

I examined the definition bodies with their docstrings removed before comparing them with the accompanying descriptions. The inventory is **38 definitions, abbreviations, structures or inductive declarations, and 65 sorried theorems**: Stage2 has 23 and 36, NDSlice has 0 and 2, and LanguageExtensions has 15 and 27. All 103 receive individual treatment below. Supporting proved theorems were used through their statements, rather than audited by reviewing their tactic proofs.

The supplied environment has neither `lean` nor `lake` on PATH and does not contain the `oleans-f7` snapshot. Thus the mathematical arguments below are my audit, while Lean execution results remain supplied-log evidence. I independently reran the byte/count checks, source inventory, width checks, style checks and corrected draft comparison. I independently consulted the relevant published-book passages through the indexed external copy identified below; I did not obtain a complete local PDF.

## Findings table

Severity follows `audits/TEMPLATE.md`. A “no findings” row is an explicit disposition of the indicated topic, not a claim that a proof has been filled.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| F1 | minor | `scripts/stmtdiff.py:decls`; pack and log §8 | The draft comparison did not compare every declaration. | The dictionary uses the last name component. It drops `XSteps.trans`, `StepsIn.mono`, `HaltsWithin.mono`, and `EndsIO.coin` through overwrites. A comparison retaining the written qualified names gives **52 identical, 5 changed, 0 missing, 2 added** for Stage2, and **38 identical, 1 changed, 0 missing, 3 added** for LanguageExtensions. The four omitted declarations are unchanged. | Key by qualified declaration identity, reject duplicate keys, and correct the two totals. Include section-variable contexts in any future claim of full elaborated-statement equivalence. |
| F2 | minor | `Randomized/Classes.lean` attribution, as expressly submitted by the pack; `Stage2.exists_simulation` deviation paragraph | The remaining AB09 attribution needs correction. | The published alternative BPP definition is **Definition 7.3, p.126**, not 7.4. Also, Exercise 1.9 uses a symbol array; “bit array” is an unnecessary specialization. The proposed `acceptProb` citation to §7.1 is sound. | Cite published Definition 7.3 for the certificate formulation; use “symbol array” in the RAM comparison. Check the supporting file's related BPP cross-reference against published Definition 7.2. |
| F3 | minor | `LanguageExtensions.XExec.bounded`, `Compiler.XFits`; PROG-2 edit table for `Compiler/Simulation.lean` | The new positivity premise creates an integration obligation not discharged by `XFits` or the input-length premise. | With `lim.word = 0`, empty input, zero initial state and a true coin, the initial state is bounded and the final local value is 1, hence unbounded. `XFits` is satisfiable: take W=8, space=0, N=Q=0; all four old fit inequalities and `input_le` hold. Existing simulation calls at lines 277 and 356 use the old boundedness theorem without this premise. | Explicitly record how the edited compiler supplies `1 ≤ lim.word` at these sites, for example as a compiler invariant/premise, or use a separately proved enlarged invariant. Do not infer it from `input_le`. The proposed boundedness theorem itself is correct. |
| F4 | minor | Pack “Names” and “Cited names” attestations; `names.py`, `cited.py` | The screens are narrower than their universal wording. | `names.py` scans explicit source declarations, not all generated Lean environment names. `cited.py` filters backticks by a regex and then excludes lowercase unqualified tokens without underscores; it does not extract every backticked identifier. No actual collision or additional unresolved cited dependency was found. | Describe the exact screened population, or use environment-based name enumeration and an exhaustive classified citation inventory. Preserve the distinction between source screening and elaboration evidence. |
| N1 | note | Stage2 A and D; brief 1 | **No findings:** the bound shapes support the specified machine. | Immediate addresses are program constants; indirect addresses are signed words. Table scans, bounded input seeks, quadratic multiplication and one-time word-size computation fit the stated expressions, including width zero. | No statement change. Preserve the representation and tape-envelope obligations described below. |
| N2 | note | Stage2 C; brief 2 | **No findings:** both word-size bridges are mathematically justified. | The logarithmic bridge needs a time lemma in addition to the existing space-only witness. The constructible-space bridge intentionally leaves time uncontrolled. | Fill the explicitly identified time lemma or use the existing time-and-space length routine. |
| N3 | note | `exists_ndSimulation`; brief 3 | **No findings:** all-stream bounds are the right sufficient hypothesis. | Every padded TM branch corresponds to a finite sequence of RAM coin outcomes, including exhausted-stream false completion. The accepting TM output must be exactly `[true]`. | Give the coin phase deterministic setup/cleanup surrounding one genuine choice transition. |
| N4 | note | Nine corollaries; briefs 4 and 7 | **No findings:** all nine follow with the stated grades. | The arithmetic is checked explicitly below, including no cell hypothesis for P, degree `3d+1`, and `S ≥ 1` for the square-space grade. | No statement change. In the logarithmic-word P proof promote the polynomial degree to at least 1. |
| N5 | note | Footprints and compiler interface; brief 5 | **No findings:** touched cells and the compiled region suffice. | The apparent return-slot omission disappears when the callee epilogue is charged to the calling statement's region. The universal-memory straight-line lemma is strong but valid. | Use run-specific footprint lemmas for useful indirect-memory bounds. |
| N6 | note | Wrapper and edit list; briefs 6 and 8 | **No additional semantic findings** in the supplied edit surface, apart from F3. | The wrapper preserves old RAM files and requires mixed code, configuration and run relations in the compiler. The 38 existential-witness lines are accounted for. Whole-repository absence claims exceed the supplied subset. | At PROG-2 fidelity review check the complete tree, and explicitly supply a code-at relation for `List XInstr`. |
| N7 | note | NDSlice; brief 9 | **No findings:** both slice statements are true. | Equality holds at every prefix, so the visited sets also agree. No agreement is needed at the final endpoint before its next transition. | Land these core lemmas before nondeterministic simulation fill; defer a contract-level variant until needed. |
| N8 | note | LanguageExtensions; brief 10 | **No findings** in the stream semantics or new rules, apart from F3. | Common-prefix determinism, stream exhaustion as failure of `EndsIO`, and existential `XEnds.coin` are consistent. RAM false completion and language stream exhaustion are different conventions requiring a padding bridge. | Add the useful padding, append and derived loop rules listed below; do not identify the conventions without hypotheses. |
| N9 | note | Bool implementation route; brief 11 | **No findings:** the route is credible. | Fixed-width fields, blank delimiters, dedicated key/ruler tapes and bounded head excursions suffice. A larger alphabet and a missing nondeterministic alphabet-reduction theorem are avoidable. | Record the concrete contracts as fill obligations. |
| N10 | note | Proposed homes and sequencing; brief 12 | **No findings:** approve the topic split, model namespace and `initMem`. | `Extended` stays below the compiler. Compiler-private footprint work belongs in the vendored compiler modifications. The imported randomized-class module is currently acyclic. | Prefer moving `acceptProb` to the Complexity side; distinguish bootstrap cut checks from actual file installation. Details below. |
| N11 | note | Documentation, policy and duplication; brief 13 | **No additional findings**, apart from F1, F2 and F4. | Every sorry has a sketch; widths are at most 100; the 1024-line elaboration unit has an explicit split. No copied proved implementation family requiring acknowledgment was found. | Apply the declared headers, attribution and NOTICE changes at landing. |
| N12 | note | Remaining attestations and brief 14 | **No additional mathematical findings.** Some historical and execution claims remain attestations. | The bundle substantiates source facts and contains consistent execution logs, but is not a repository snapshot, an olean snapshot or independent provenance proof. | Retain the evidence qualifications in this report; do not turn them into claims of independently reproduced execution. |

## Rulings on the fourteen brief points

### 1. Simulation bounds and representation

The address of an indirectly touched cell is a signed W-bit integer. An immediate operand can be arbitrarily larger, but the finitely many such operands belong to the fixed program. Store keys using a fixed program-dependent extension of the word width, or distinguish these exceptional addresses separately; either construction has entry size at most a program constant times `W+1`. No input-dependent address-width parameter is missing.

A table can contain at most the touched addresses plus the initial length cell, so at most `f+1` entries. A lookup compares each fixed-width key against a key tape and rewinds that tape after each comparison, costing O(W+1) per entry. All table scans must remain in the occupied table interval; merely bounding each individual instruction's space would not control accumulated visited cells if scratch heads drifted between calls.

R8.5b's previous input position is bounded by `n+1` because the input-head type is bounded. A valid zero-based RAM bit position is translated to the input tape's position convention; the range test prevents an unbounded seek. The seek therefore costs O(W+n+1), and the range test's O(logSpace n) work/time is covered by the existing space/time terms. At W=0, use the constant allowance rather than insisting that a positive tape position has a zero-bit encoding.

Multi-tape shift-and-add multiplication uses W rounds of O(W) work, O(W²) time and O(W) scratch. The initial length scan and construction of the ruler cost O(n+W²+1); `t+1` covers this startup even for the smallest admissible halt, where `t=1`. The extra initial table entry, empty encodings, blank endpoints and initial positions of a fixed number of simulation tapes are covered by the `W+1` and final `+1` terms.

The coefficient of `TW` and `SW` is literally one. The fill must embed the word-size witness in lockstep, preserve its source work-tape bank after it halts, and use separate simulation scratch. Capturing its output adds at most O(W+1) visited cells; resetting the source work bank or repeatedly interpreting its transitions with a slowdown would not establish the displayed bound. The supplied silent embedding gives a credible route. The theorem's quantifier order permits A to depend on the fixed word-size witness as well as P; prose asserting dependence on P alone is stronger than what is needed or formally asserted, although an exact embedding can plausibly achieve that stronger uniformity.

### 2. Word-size hypothesis

`WordSizeComputable` requires one finite machine for all inputs, with binary output and simultaneous time/visited-space bounds. It cannot smuggle an arbitrary uncomputable width function into the simulation. Its bounds need not themselves be computable, which is harmless: they are bounds, not inputs to the constructed simulator.

The logarithmic bridge is true, including c=0 and n=0. Obtain the binary input length in linear time, arrange a bit string of length `logSpace n`, count that short string and multiply its length by the fixed c. Even a quadratic-in-logarithm pass is O(n+1); the space-only theorem alone does not prove this time assertion, so the stated extra time argument remains necessary.

For the constructible-space bridge, capture the constructibility witness's binary output, multiply by c and emit it. The captured representation and arithmetic use O(log(S+1)+1) cells, absorbed by O(S) since S is at least 1. Taking a maximum of halting times over the finitely many inputs of each length supplies some `TW`; the square-space consumer imposes no bound on that function.

### 3. Nondeterminism and all branches

Uniformity over all finite streams is sufficient and appropriate. A TM branch supplies choices even at deterministic states; extract just the bits occurring at actual coin choices. Conversely, any requested RAM prefix can be placed at those choice positions, and subsequent padding is irrelevant after halt. An arbitrary infinite choice sequence has a sufficiently long finite prefix, and the common t prevents a branch from escaping the hypothesis by requesting ever more coins.

The coin instruction needs deterministic lookup, preparation of the destination word and cleanup, with exactly one transition at which the two choices differ. It cannot literally perform arbitrary table lookup and write a whole word in one physical TM step. This is an implementation clarification of the sketch, not a counterexample to its bound or theorem.

The slice lemma handles deterministic stretches, but does not alone prove the all-branch space claim. The representation invariant and tape envelopes must also hold at the choice transition and for either resulting bit. Verdict mode suppresses RAM `emit` instructions and writes precisely the terminal verdict, matching `FinNDTM.AcceptsWithin`. C2 programs must reject bad guesses within their common bound; a possibly infinite bad-guess loop does not meet this sufficient interface.

### 4. Logspace grade

For `W=c·logSpace n`, fixed footprint `F₀`, and bridge space `a·logSpace n`, the bracket in the simulator's space bound is at most

`(a + F₀·(c+1) + c + 2)·logSpace n`.

This uses `logSpace n ≥ 1`, including at empty input. Input is read in place, emitted output is streamed to the uncounted append-only output, and the simulator need not maintain the RAM's mathematical coin counter in binary. Thus neither input length, output length nor running time enters work space as an additional linear quantity.

### 5. Footprints and compiler region

The touch sets include every RAM cell whose value is read and every destination, including both address registers and indirectly addressed cells. Counting reads as well as writes is conservative for a sparse memory table and implements the binding decision. Neither input positions nor coin/output positions are RAM addresses.

For `stepsIn_straight`, “all memories” forces K to contain all **signed W-bit addresses** reachable by an indirect operand, plus the literal operands; it does not force all of ℤ for a fixed finite W. The lemma is useful for direct arithmetic and deliberately coarse for indirect operations. The needed precise compiler proofs should use actual-state relations and segment-specific footprint lemmas.

`Touchable` contains scratch, frame pointer, the remaining stack segment, the language memory interval and constants. FP-relative loads of variables stay in the current frame by the width/room hypotheses. On a call from frame q, the callee frame is `q+F+1` and its return slot is `q+F`; that slot belongs to the caller's stack segment. The return of the currently simulated procedure is not part of the simulation of its body alone. This resolves the proposed return-slot objection.

The region is the integer interval from `-lowCell` inclusive to `lim.space` exclusive, of cardinality `lowCell+lim.space`. Startup, body and tail use only that region. Their counts give a nonverdict prefix strictly shorter than `ramSteps`; the final verdict is the remaining counted step. The initialization bridge supplies the compiler's input representation using the zero language memory, argument 1 equal to input length and argument 2 equal to zero. Its explicit length bound supplies bounded input; neither arbitrary untouched initial cells nor the excluded input tape invalidate the footprint claim.

### 6. Wrapper decision

The supplied wrapper follows the binding decision: it adds no constructors to the old `Instr` or fields to the old `Cfg`. The old calculus lifts on base-only segments, while projection of a new instruction is rejection; the projection bridge makes no converse or verdict-preservation claim for such instructions.

The real compiler edit must change code types, execution configurations and run relations, and preserve output/coin state across base segments. It also needs a code-at relation that locates actual `XInstr` instructions: projection alone erases which new instruction occupied a position. This is part of the recorded code-type work, not an argument to reverse the wrapper decision. The estimate of about 50 anonymous literals is only an estimate; this bundle cannot verify its whole-tree population.

### 7. Nine corollaries

All nine are individually justified in the theorem ledger. For the P grade, let the common polynomial bound be `C·(n+1)^d`. Use footprint `3C·(n+1)^d`; then the time bracket is bounded by

`[C + (C+1)·(4C²+3C+1)]·(n+1)^(3d+1)`.

The extra simulator factor can be absorbed by `A+1`. This works at d=0 as well. The logarithmic-word specialization must enlarge the common degree to `max d 1` and enlarge the coefficient to cover the linear-time width computation.

For the square-space grade, `logSpace ≤ S` gives `S≥1`, and the displayed coefficient `a+c²+2c+2` is valid. The transducer statement concludes the repository's `ComputesInSpace`, not its own assertion of an AB09 reduction predicate. Its declaration of the different conclusion is appropriate. Moreover, a deterministic halting append-only logspace transducer has polynomially many internal configurations, hence polynomial running time and output length: repeating an internal configuration would repeat its future forever because prior output cannot affect a transition. That equivalence still needs an exported bridge if downstream work wants to use an implicit-output reduction interface.

### 8. Edit-list completeness

Within the supplied sources I confirmed the seven-arm syntax/compiler matches, `length_compileStmt`, width lemmas, assigns induction, four Exec inductions, the compiler simulation cases, whole-program theorem, block-rule term match and wildcard block classifiers. The six files naming `Exec` and the constructor uses in `Rules` are accounted for. The witness count is 28 in `Logic`, 8 in `Rules` and 2 in `Assigns`, totaling 38, as the corrected pack states.

The explicit `List Instr`/`CodeAt` sites listed by the pack are the right type-changing surface. Base expression, call, epilogue and dispatcher segments can remain old code and be mapped into the wrapper. F3 adds a concrete hypothesis-propagation obligation at the existing intermediate-state boundedness calls. Mixed-code location and extended `FinishedIn`/whole-program footprint statements must be included in the PROG-2 fidelity gate.

I found no relevant missed match or witness destructuring in the supplied `Frames`, `Calls` or `Tactics`. The bundle does not include the complete `Lib/` tree or `Regions.lean`; consequently I cannot independently certify the “no site anywhere in Lib/” or “no Limits construction anywhere” attestations. Those need a full-tree check at the scripted edit. No supplied counterexample to those absence claims was found.

### 9. Slice lemma

Both statements are true for arbitrary tape count, alphabet and state type; finiteness is unnecessary. The hypothesis concerns the states visited by the fixed-choice run before each transition. Induction proves that the arbitrary-choice run has reached the same state and tape contents at those times, so the hypothesis is available exactly where needed. A halted configuration remains fixed, and equality for all prefixes yields equality of the visited sets including their final endpoints.

This is the right run-level tool for the intended Bool machine between coins. MIG-0b need not be expanded now solely for this use; add a contract-level wrapper when a consumer requires its compositional interface.

### 10. PROG-2 mirror

The common-prefix determinism theorem is correct. Two completed executions whose consumed strings are prefixes of the same stream cannot disagree at their first coin, and after equal prefix executions their remaining streams are equal drops. This pins down state, output, consumed word and cost. `XEnds` deliberately forgets the stream; its coin rule is existential. This is harmless for the existing coin-free routines, although it must not be used as a fixed-stream rule for a coin-bearing algorithm.

`EndsIO` gives no execution to a coin on an empty stream. RAM `coin` instead supplies false after exhaustion. The natural compiler connection uses sufficiently long streams, for example length at least the language cost bound, or explicitly false-pads a stream; a literal equivalence on all short streams would be false.

The existing loop step/done rules suffice to derive invariant and variant rules, but those derived rules would materially improve C2 proofs. The global IOFree bridge requires every program body to be IOFree; it does not directly lift an old routine inside a whole program already containing coin code. One can first lift the pure library and then use execution/program append, or prove purity only for the reachable callees. An `EndsIO.append` convenience lemma is appropriate.

`XFits.input_le` follows in the whole-program setting when the compiler input argument really is `lim.input.length` and its `Input` invariant holds. It does not follow from old `Fits` alone, and it does not imply positive `lim.word` on empty input. See F3. Leaving `inBit` and `half` outside the block fragment is safe and matches the existing wildcard definitions; adding them as blocks is an optional language-automation extension requiring definitions and lemmas, not a missing semantic axiom.

`acceptProb` is the finite uniform counting probability of accepting within T with m available coins. Runs needing more than m coins are absent from that event. Since a run consumes at most its cost, m≥T suffices to remove exhaustion as an additional restriction; further coin padding then leaves the probability unchanged. The definition by itself asserts neither totality on every stream nor membership in a randomized complexity class.

### 11. Alphabet

Bool is sufficient. The machine's tapes actually have blank cells in addition to Boolean symbols, and fixed-width fields can be traversed with a ruler and finite-control phase information. Comparing a key against successive table entries and doing digit arithmetic require neither an input-dependent finite alphabet nor random access on the TM. Keep fixed scratch envelopes and explicit zero-width cases in the contracts. I approve this route without requiring a public per-input alphabet reduction or a nondeterministic analogue.

### 12. Homes, names and sequencing

Approve `Programs/WordRAM/Extended`, the compiler additions B1/B2, `Complexity/RAMSimulation/{WordSize,Simulation,Classes}`, namespace `WordRAM`, and `initMem`. They separate model semantics from simulation and classes, avoid the proposed import cycle, and avoid the existing compiler `startMem` name. The core slice lemmas belong beside their deterministic special cases.

B1/B2 may land first against the current compiler, with an explicit obligation to re-gate their extended counterparts when PROG-2 changes code and run types. Alternatively, land them with PROG-2; there is no mathematical requirement to postpone the current statements. Do not leave the old forms advertised as the extended compiler theorem. The mirror-only bridges are evidence and should not become permanent duplicate language definitions.

I recommend putting `acceptProb` in a Complexity-side module while retaining its `Light` namespace. The current import of `Randomized.Classes` is acyclic, but separating the probability-facing adapter keeps the existing Programs dependency boundary and costs little. This is a module-home ruling, not a soundness defect.

The cut checks are bootstrap elaboration checks over old imported modules plus appended parts. They are not actual installation builds. In particular B1/B2 must retain their upstream file contents and copyright headers, append their new declarations, and gain actual dependencies; their probe self-imports must not become installed self-imports. Resolve the “literal cut” prose in that sense, consistent with the pack's explicit “appended” table.

The facade generator already discovers `.lean` children through `kids`/`tree`, so it automatically sees the two new files; its descriptions/attribution may need adjustment, not necessarily new discovery logic. Apply the NOTICE exceptions, vendored local-modification headers, root/facade imports, registry entry and design rename listed by the pack. Use the explicit landing-name mapping: mechanically deleting an uppercase X is not a sufficient renamer for `xmainStmt` or `of_xEnds_ioFree`.

### 13. Documentation, attribution and duplication

All three units have source attribution and statement prose; all 65 sorries have preceding proof sketches. Maximum line widths are 99, 100 and 100. The independent style run gives zero FAIL and one WARN, solely the Stage2 elaboration unit's 1024 lines; its six-way landing split is an adequate justification. Empty “Main definitions” sections need not be invented for theorem-only additions.

The AFM26 adaptation entries supply project, pinned full commit, date, licence and relevant paths. The pending NOTICE/header changes are necessary at landing, rather than defects in these unlanded evidence units. The cumulative duplication screen finds zero copied proved implementation blocks in Stage2, zero in NDSlice and zero landing copies of proved implementation blocks in LanguageExtensions. The latter deliberately restates syntax and logic with new indices as a temporary specification; its old-language bridges are explicitly not to land. Stronger footprint theorems are new obligations, not unapproved private copies of existing proofs. No debt-family acknowledgment is required by this packet.

### 14. Other observations

The packet should preserve the difference between a useful sufficient interface and an equivalence of models. `HaltsWithin` asks for a finite touched set; the simulator can materialize only written cells, but this does not change the chosen accounting. The deterministic theorem uses the empty stream and may apply even to programs containing coins, with those coins fixed to false. `CoinFree` is sufficient for stream independence, not necessary; a dead coin instruction can make it false without affecting an actual run. These are intentional strengths or conventions, not class collapses.

## Attestation ledger

| Attestation | Audit disposition |
|---|---|
| Bundle identity and 82 sections | Independently verified on the complete original bytes, before section extraction. |
| Three Lean elaborations, Lean v4.25.0, 0 errors, 36/2/27 sorry warnings | The supplied log reports these results, and the source sorry counts match exactly. Not independently re-executed without the toolchain/snapshot. |
| Maintainer's separate re-check and separate cut-verification script | This is an additional attestation, not independently evidenced by a separate supplied transcript/script. I cannot certify independence of the executions. |
| Six cut checks and own-import union | The supplied algorithm constructs the advertised dependency closures; their source sorry totals are 18, 19, 22, 3, 23 and 32. The log reports successful elaboration. Existing-module self-imports serve the bootstrap check only; actual landing remains to be built. |
| 24 Stage2 and 15 language probes | Source counts and stated cases checked. They exercise definitions rather than treating the 65 proposed theorems as proved. Their successful Lean execution and the three one-error negative controls are log-supported, not rerun here. |
| Style lint | Independently reproduced: 0 FAIL, 1 WARN; declaration counts 59/2/42, all public. The WARN has a supplied split justification. |
| Widths | Independently reproduced: maxima 99/100/100; no line exceeds 100. |
| Names: 103 and no clashes | 103 explicit declarations verified; no clashes found against the supplied supporting declarations. The full-tree claim and positive-control execution are log-supported. The source screen's scope needs F4's qualification. |
| Cited-name checks | The extractor and unresolved-name list were inspected. Bound variables, module paths, private lemmas, future names, unimported names and mirror landing names explain the supplied unresolved cases. “Every” needs F4's correction. |
| Draft correspondence | Independently challenged and corrected by F1. No additional changed declaration was found among the omitted four. Text normalization is not a comparison of fully elaborated types with section binders. |
| Nothing changed in the maintainer worktree; no git/lake/olean output | The supplied scripts are consistent with scratch-only checks, but historical absence of writes cannot be inferred conclusively from this bundle. I did not modify the attached input. |
| Campaign commit and intervening changes | The stated history is not authenticated by a git checkout/diff in the bundle. Checked cited source locations are consistent with the attached contents. |
| Complete edit/absence scans | Confirmed for the supplied relevant sources, with the explicit missing-tree qualification in point 8. Counts described as regex estimates remain estimates. |
| Upstream footprint bytes | Independently verified 129 lines and SHA-256 `0d6c6b09c4fa276671e2116246767aee9c478c7d72adfc49838c55fe015588f9`. |
| Upstream footprint provenance | Matching two other file hashes is evidence consistent with the pinned tree, not proof that this footprint blob is from that commit. The pack correctly labels its conclusion “presumably.” |
| Upstream footprint mathematical role | Its theorems provide write/change counts and a bounded read-dependence certificate; they do not provide a run staying within a prescribed region. `exec_congr` exposes preservation of verdict within the given fuel, not an explicit exact trace footprint. It complements, rather than replaces, `StepsIn`; a time-proportional count alone does not supply the intended L footprint. |
| Binding decisions | Wrapper, in-place Exec indices, computed width, nonzero output, touched-cell accounting, in-place input, read-once coins, halving and all-stream bounds are all reflected in the proposed definitions. |

## Independent AB09 location check

Reference: S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009. I used the published-page text in this [external copy](https://kubokovac.eu/zlozitost/arora.pdf), not the bundle's assertions. Relevant pages were available through indexed retrieval; direct PDF retrieval was unavailable.

| Location | Ruling |
|---|---|
| Definitions 1.12–1.13, p.25 | DTIME and P locations correct. |
| Exercise 1.9, p.35 | RAM simulation and quadratic-time comparison correct; symbol array. |
| §2.1.2, p.41 | Two transition functions and universal branch time bound confirmed. |
| Definition 4.1, pp.78–79 | Space location correct; the text's nondeterministic nonblank-cell convention differs from this repository's visited-cell convention. |
| Definition 4.5, p.81 | L and NL location correct. |
| Theorem 4.14, p.86 | Savitch location correct. |
| Definition 4.16, p.88; Exercise 4.8, p.94 | Implicit-output and write-once-output comparison correctly located. |
| §4.3.1, Definition 4.19, p.90 | Read-once certificate location correct. |
| §7.1, pp.124–126 | Appropriate for `acceptProb`; published PTM/BPP/alternative-BPP definitions are 7.1/7.2/7.3. |

The repository's visited-cell convention and its explicit transducer conclusion are acceptable declared model choices. The new word-RAM resource formulas and footprint definitions are the repository's own refinements; the book citations do not purport to supply these exact statements.

## Definition ledger: all 38 declarations

Line numbers below refer to the original proposed `.lean.txt` sections. These restatements came from the bodies; the final column records the subsequent prose/source comparison. Constructors and structure fields are included in the restatement of their parent declaration.

### Stage2: 23 definitions

| ID | Declaration · line | Independent mathematical restatement | Fidelity ruling |
|---|---|---|---|
| D1 | `WordRAM.XInstr` · 131 | An instruction is either one of the nine old instructions, or input-read with destination and index cells, output of a cell, coin into a cell, or arithmetic halving from a source cell to a destination. All named RAM cell operands are integers. | Implements the wrapper decision; no new constructor of the old instruction type. |
| D2 | `WordRAM.XProgram` · 139 | A program is a finite list of extended instructions; list positions are its instruction addresses. | Matches the declared finite program model. |
| D3 | `WordRAM.XCfg` · 144 | A configuration contains the old natural program counter and total integer-addressed W-bit memory, plus a finite Boolean output and a natural consumed-coin count. | The count/output are semantic state, not a claim that the simulator stores them as work-space words. |
| D4 | `WordRAM.inBitWord` · 152 | Return the W-bit numeral 1 exactly for a nonnegative index whose input bit exists and is true; otherwise return the W-bit zero. | Matches negative/out-of-range defaulting. At W=0, the two numerals coincide; at W=1, the signed value of numeral 1 is −1. |
| D5 | `WordRAM.coinWord` · 156 | Encode false by the W-bit zero and true by the W-bit numeral 1. | Correct modular encoding, with the same tiny-width qualifications as D4. |
| D6 | `WordRAM.xstep` · 163 | Fetch the instruction at the program counter, defaulting to reject. Base instructions follow old stepping; new instructions update input destination, append nonzero output, consume/default a coin while incrementing its count, or arithmetic-shift the source right once, then advance the counter. A verdict is returned separately from continuing configurations. | All old cases and new effects match the specified semantics; output means nonzero, not positive. |
| D7 | `WordRAM.XSteps` · 180 | An exact-length chain of continuing extended steps, with equality at length zero. Its last configuration has not yet been required to produce a verdict. | Correct counterpart of the vendored run relation. |
| D8 | `WordRAM.CoinFree` · 185 | No list element of the program is any coin instruction. This is a syntactic property of the entire list, including unreachable entries. | Stronger than semantic stream independence, intentionally sufficient. |
| D9 | `WordRAM.XProgram.proj` · 192 | Preserve each base instruction and replace every new instruction by old rejection, without changing list length or positions. | Correct for lifting nonverdict base segments; not an erasure preserving arbitrary extended executions. |
| D10 | `WordRAM.baseTouches` · 248 | The touched set is the destination for `one`; the three operands for arithmetic; destination, pointer register and pointed-to cell for load; both registers and pointed-to destination for store; the test register for branch; and empty for either verdict. | Includes every read and write; aliases reduce cardinality automatically. |
| D11 | `WordRAM.XInstr.touches` · 263 | Use D10 for base instructions; input-read and half touch their two named cells, while emit and coin touch their single named cell. | Input/coin/output media are deliberately not counted as RAM cells. |
| D12 | `WordRAM.XStepsIn` · 281 | An exact extended run whose touched set at every continuing step is contained in the supplied integer set K. K need not itself be finite here. | Correct touched-footprint refinement of D7. |
| D13 | `WordRAM.StepsIn` · 290 | The same exact-run/touch-containment requirement for the old RAM. | Correct compatibility layer for the current compiler. |
| D14 | `WordRAM.initMem` · 394 | Start with zero everywhere, except integer cell −1 contains the W-bit encoding of the natural input length. The length is reduced modulo the word modulus. | Matches compiler argument cell 1 without importing the compiler; no assumption that the length fits is built into this RAM definition. |
| D15 | `WordRAM.XCfg.init` · 399 | Initial counter zero, memory D14, empty output and consumed count zero. | Correct whole-program initial convention. |
| D16 | `WordRAM.HaltsWithin` · 405 | There exist a continuing prefix of n steps, an endpoint and a finite K, with n<t and cardinality at most f, such that the prefix stays in K and the endpoint produces verdict v with output o. | Counts the final verdict in the time budget. Initial cells are not automatically “touched”; verdicts touch none. |
| D17 | `Light.Compiler.Touchable` · 478 | The compiler's writable region for this layout/frame, enlarged by its constant-register/pool region. | Appropriate additional reads beyond writable cells, subject to the frame analysis in point 5. |
| D18 | `Light.Compiler.FinishedIn` · 482 | A `Finished` witness with all its execution, cost, representation and outside-write guarantees, plus a touch-bounded old-RAM run with exactly the same endpoints and step count. | This is a real strengthening; it does not replace touched containment by merely unchanged memory. |
| D19 | `Light.Compiler.region` · 536 | The finite integer interval with lower endpoint minus the compiled layout's `lowCell` and upper endpoint `lim.space`, excluding the upper endpoint. | Contains reserved negative cells and the allowed nonnegative language memory. |
| D20 | `WordRAM.WordSizeComputable` · 639 | Some single finite Boolean TM outputs `Nat.bits (W n)` on every length-n input, by some time at most `TW n`, and visits at most `SW n` work cells through that time. | Correct uniform computability and simultaneous resource hypothesis; it is deliberately distinct from either single-resource constructibility predicate. |
| D21 | `WordRAM.simTime` · 747 | The width-computation budget plus A times `t+1` times the sum of table size `f(W+1)`, multiplication allowance W², input length n and one constant unit. | Agrees exactly with the proposed explicit overhead. |
| D22 | `WordRAM.simSpace` · 752 | The width-computation space plus A times the sum of table size `f(W+1)`, word scratch W, logarithmic input-length storage and one constant unit. | No dependence on RAM time, coin count or output length; this is the required space interface. |
| D23 | `WordRAM.outputOf` · 758 | In function mode choose the emitted word; in verdict mode choose the singleton containing the verdict. | Matches `ComputesInTime` and decision-class conventions. |

### LanguageExtensions: 15 definitions

| ID | Declaration · line | Independent mathematical restatement | Fidelity ruling |
|---|---|---|---|
| D24 | `Light.XStmt` · 93 | The old seven statement forms plus input-bit assignment, output of an expression, coin assignment and halving assignment. Variables/procedure identifiers remain natural numbers, and the old expression/condition types are reused. | Correct mirror of the requested syntax change. |
| D25 | `Light.XProgram` · 108 | A finite list of extended procedure bodies, indexed by natural procedure identifiers. | Same program organization as the old language. |
| D26 | `Light.XLimits` · 113 | Old integer value bound, natural memory-space bound and natural depth bound, together with one fixed input bit list. | Input is immutable through an execution; no automatic positivity premise is introduced. |
| D27 | `Light.inBitVal` · 120 | The integer 1 for a true input bit at a nonnegative in-range index, and integer zero otherwise. | Matches the specified input convention; unlike D4, this is an integer value without modular collapse. |
| D28 | `Light.XExec` · 129 | A finite big-step derivation between language states, indexed by emitted bits, consumed coin bits and cost. Skip costs zero; safe assignments/stores add their expression costs plus one; sequence concatenates the two logs and adds costs; branches and loop tests add condition cost plus one; calls check body lookup/depth, evaluate safe arguments, execute in a new frame, restore the caller with local 0 returned, and pass logs through with argument cost plus two. Input and half cost expression cost plus one; emit leaves state unchanged and emits nonzero; coin chooses either Boolean, writes its integer encoding and records it at cost one. | All 13 rules match option A. Safety of intermediate boundedness for a generated 1 needs the separate positive-bound premise, correctly present in the theorem rather than silently built into this relation. |
| D29 | `Light.XStmt.assigns` · 172 | A syntactic list of caller-local variables possibly assigned: concatenate across sequence/branches, recurse into loops, use the result variable for calls, and include the targets of set/input/coin/half; store and emit contribute none. | Correct local-frame accounting; callee internal locals are not caller assignments. |
| D30 | `Light.XEnds` · 237 | There is a completed extended execution of cost at most T ending in a state satisfying Q, with both logs existentially hidden. | Retains the old predicate's external type and its existential reading. |
| D31 | `Light.xmainStmt` · 244 | Call procedure p0 with caller locals 1 and 2 as arguments and put its return into local 0. | Exact mirror of the existing main-call convention. |
| D32 | `Light.Compiler.XFits` · 253 | All old word/address/stack/pool fit inequalities hold for the old portion of the limits, and the input length is at most the integer value bound. | Correct added condition, conditionally redundant when the matching whole-program input invariant is already supplied; see F3 for what it does not imply. |
| D33 | `Light.XStmt.IOFree` · 298 | Exclude emit and coin, recurse through sequence/conditional/loop, and accept all other forms, including calls. Calls are certified separately by a program-wide body condition in the purity theorem. | “IOFree” here means no output or coins; it permits input reads. The body makes this clear. |
| D34 | `Light.EndsIO` · 323 | There is a completed execution of cost at most T whose consumed coin list is a prefix of the supplied finite stream, and whose state, output and consumed list satisfy Q. | Correct fixed-stream partial-execution predicate; short streams are not false-padded by this definition. |
| D35 | `Light.MeetsIO` · 479 | A named procedure body exists and, when started at the chosen depth with the listed argument frame and memory, meets an `EndsIO` postcondition expressed through its return local, final memory and two logs. | Appropriate specification-only call interface adapted from `Meets`. |
| D36 | `Light.AcceptsND` · 505 | Some stream of exactly T bits makes the outer main call from the designated initial frame and memory finish within T with positive return value. | A bounded existential acceptance event; universal halting is not asserted here and must be supplied separately for class consequences. |
| D37 | `Light.acceptProb` · 515 | Apply the finite uniform m-bit counting probability to that bounded positive-return event, using the specified input, auxiliary argument, memory and time budget. | Correct finite-coin event. Noncomputable proposition selection does not claim an efficient decision procedure or randomized-class membership. |
| D38 | `Light.XStmt.ofStmt` · 525 | Recursively embed each old statement constructor, preserving procedure identifiers, expressions, conditions and destinations. | Correct temporary comparison map; programs must be mapped bodywise as well. It has no post-edit landing counterpart. |

## Theorem ledger: all 65 sorries

Each entry gives a mathematical argument for the literal statement. These arguments do not treat another proposed sorry as an established Lean proof; when a corollary depends on a proposed theorem, that dependency is stated and its mathematical construction is separately examined above.

### Stage2 A: 18 theorems

| ID | Declaration · line | Argument |
|---|---|---|
| T1 | `WordRAM.XSteps.trans` · 206 | Induct on the length of the first run. Its zero case substitutes the intermediate configuration, and its successor case preserves the first continuing step and concatenates the remaining runs. |
| T2 | `WordRAM.xstep_map_base` · 218 | Fetching from a mapped program produces the mapped old instruction, including default rejection beyond the end. Case analysis on that instruction shows the same old configuration update or verdict, while output and consumed count are unchanged. |
| T3 | `WordRAM.XSteps.of_steps` · 227 | Apply T2 to each continuing step of the old run. Induction preserves the fixed output and consumed count and gives the exact same number of extended steps. |
| T4 | `WordRAM.XSteps.of_steps_proj` · 237 | Any continuing step of the projected program must come from a base instruction, since a new instruction projects to immediate rejection. Lift those steps successively; the claim does not try to lift a projected verdict at a new instruction. |
| T5 | `WordRAM.XInstr.card_touches_le` · 274 | Each constructor explicitly yields a finite set presented with at most three elements. Repeated operands and indirect aliases only reduce its cardinality, so no distinctness premise is required. |
| T6 | `WordRAM.StepsIn.toSteps` · 302 | Forget the touch-subset conjunct at each successor. The remaining recursion is exactly `Steps`, including its zero case. |
| T7 | `WordRAM.Steps.exists_stepsIn` · 312 | Take the finite union of the touched sets along the exact run. Each of its n continuing steps contributes at most three elements, so the union has cardinality at most 3n and satisfies every containment obligation. |
| T8 | `WordRAM.StepsIn.mono` · 319 | Compose each touched-set inclusion with the inclusion of K in the larger set. The transition witnesses and endpoints remain unchanged. |
| T9 | `WordRAM.StepsIn.trans` · 327 | Enlarge both footprints into their union using T8. Induction on the first run then concatenates the exact runs with that common footprint. |
| T10 | `WordRAM.StepsIn.agreeOutside` · 341 | Split the exact run after k steps, where k≤n, retaining its prefix and suffix. A continuing instruction either leaves memory unchanged or updates a destination included in its touched set, so induction on the prefix gives agreement with the initial memory outside K. |
| T11 | `WordRAM.stepsIn_straight` · 354 | `CodeAt` locates each straight instruction and the old straight-line calculus advances the counter while applying its memory effect. The universal-memory hypothesis applies to whichever intermediate memory occurs, so induction on the code list supplies the stronger touch-bounded run. |
| T12 | `WordRAM.XStepsIn.toXSteps` · 363 | Erase the subset condition at each continuing extended step. The recursive transition and zero-step clauses are precisely `XSteps`. |
| T13 | `WordRAM.XSteps.exists_xStepsIn` · 371 | Unite the actual touched sets along the extended run, using T5 for each step. The resulting finite union covers the run and has at most 3n members. |
| T14 | `WordRAM.XStepsIn.of_stepsIn_proj` · 380 | As in T4, a continuing projected step cannot execute a projected new instruction. At each actual base step, the old and extended touched sets coincide, so the same K and step count work. |
| T15 | `WordRAM.HaltsWithin.mono` · 417 | Reuse the prefix length, endpoint and finite footprint. The larger time preserves the strict inequality n<t, and the larger cell budget preserves the cardinality inequality. |
| T16 | `WordRAM.HaltsWithin.touches_le` · 426 | Forget the original footprint, recover a footprint of at most 3n cells using T13, and retain the verdict endpoint. Since n<t, that footprint is certainly bounded by 3t. |
| T17 | `WordRAM.HaltsWithin.unique` · 436 | The step function is deterministic for fixed program, input, stream and width. If two terminating runs differed in prefix length, the shorter endpoint would have to return both a verdict and a continuing configuration; hence their endpoints, outputs and verdicts agree. |
| T18 | `WordRAM.HaltsWithin.coin_irrel` · 443 | For a CoinFree program, every fetched instruction is independent of the stream; out-of-range fetch is rejection and is independent as well. Reuse the same exact run, finite footprint and terminal verdict in either direction. |

### Stage2 B–D: 9 theorems

| ID | Declaration · line | Argument |
|---|---|---|
| T19 | `Light.Compiler.sim_in` · 502 | Refine the existing structural simulation by proving touched containment for each emitted segment, while retaining its existing endpoints, cost and representation facts. Scratch and pool accesses are in `Touchable`; safe language addresses lie in its memory interval, and frame width/room place local and call accesses in its stack segment. A nested callee's return slot is charged to the caller's segment, as explained in point 5. This establishes the added field of `FinishedIn` without changing the old simulation claim. |
| T20 | `Light.Compiler.card_region` · 542 | The cardinality of this integer half-open interval is its upper endpoint minus its lower endpoint. Both layout depth below zero and the natural space limit are nonnegative, so the result is `lowCell + lim.space`, including a zero space limit. |
| T21 | `Light.Compiler.compileProgram_footprint` · 557 | Startup touches only the pool, fixed registers, argument cells and main frame; T19 covers the main-call body, and the tail stays in the same global region. Startup takes `disp+F+9` continuing steps, the body at most `2·disp·c`, and the tail at most 3, giving at most `disp+F+12+2·disp·c = ramSteps−1` continuing steps. The existing representation and verdict arguments give `Outcome`, and concatenating the segment footprints gives the stated region. No premise requires memory outside that region to start at zero. |
| T22 | `Light.Compiler.haltsWithin_compileProgram` · 580 | The special initial memory represents zero language memory and the two arguments `input.length` and zero, with the explicit length bound providing the required input bound. Apply T21, lift its old run and verdict through base mapping, and use T20 to bound the footprint cardinality. Output and consumed count stay empty/zero under the lift, so any external coin stream is allowed. |
| T23 | `WordRAM.WordSizeComputable.mono` · 647 | Keep the witnessing machine and its chosen halting time for every input. Compose the time and space inequalities with the new pointwise bounds. |
| T24 | `WordRAM.wordSizeComputable_logSpace` · 663 | The linear-time binary input-length routine provides a short word from which `logSpace n`, including its value at zero, can be counted and multiplied by the fixed c. These further passes take at most quadratic logarithmic time and logarithmic space, both dominated by the asserted bounds after choosing a constant. The existing space-only witness is insufficient by itself, but the additional time route named in the sketch supplies the missing argument. |
| T25 | `WordRAM.wordSizeComputable_of_spaceConstructible` · 678 | Run the constructibility machine with captured binary output, multiply by the fixed c and output the result. The extra logarithmic representation space is absorbed in O(S) because `S≥logSpace≥1`. Every input halts, and a maximum over the finite set of length-n inputs defines a suitable unrestricted time bound. |
| T26 | `WordRAM.exists_simulation` · 799 | Construct a finite Bool machine with a phase for each program position, a sparse fixed-width address/value table, and dedicated ruler, key and arithmetic tapes. Run the width witness once using exact silent embedding, preserve its work bank, then initialize the ruler, length copy and the exceptional initial cell. The operations and bounded tape envelopes detailed in point 1 implement each `xstep` within the displayed per-step time and accumulated space allowances, and the table has at most f+1 entries along a run with footprint f. In function mode stream the emitted bits; in verdict mode suppress them and emit only the verdict, so output storage is not silently charged as work space. Deterministic halting freezes the configuration, making the space bound through the possibly padded `simTime` valid. |
| T27 | `WordRAM.exists_ndSimulation` · 827 | Use the same representation with equal transition functions at deterministic states and one genuine bit choice in each coin phase. Deterministic preparation and cleanup make either choice preserve the same representation and tape-envelope bounds. A length-T branch extracts a finite RAM stream, while every RAM stream's relevant prefix can be realized by a branch with irrelevant choices padded through halt. The common RAM time and footprint bounds therefore control every branch, and accepting verdict mode emits exactly `[true]`. Slice equality handles the deterministic stretches; the explicit coin invariant handles the boundaries it does not cover. |

### Stage2 E: all 9 corollaries

| ID | Declaration · line | Argument |
|---|---|---|
| T28 | `WordRAM.mem_DTIME_of_decides` · 880 | Apply T26 in verdict mode to obtain one decider for all inputs. Its time is at most `(A+1)` times the bracket bounded by `a·T'`, so `(A+1)·a` witnesses membership in the repository's DTIME class. |
| T29 | `WordRAM.mem_P_of_decides` · 899 | By T16 every supplied run can be given footprint at most three times its time, and monotonicity pads both bounds to the common polynomial. The coefficient and degree calculation in point 7 bounds simulation time by a constant times `(n+1)^(3d+1)`. Apply T28 and the repository's characterization of P. |
| T30 | `WordRAM.mem_P_of_decides_logWord` · 913 | T24 supplies linear width-computation time, while `c·logSpace n ≤ c·(n+1)`. Enlarge the common polynomial coefficient and use degree `max d 1`, then apply T29; using the original d unchanged would overlook the d=0 case. |
| T31 | `WordRAM.mem_SPACE_of_decides` · 929 | T26 yields a halting decider on each input using its individually supplied RAM time, which need not be bounded by a prescribed function. Its space is at most `(A+1)` times the bracket dominated by `a·s`, giving a fixed space coefficient `(A+1)·a`. |
| T32 | `WordRAM.mem_LOGSPACE_of_decides` · 946 | Use T24 and instantiate T31 with the constant footprint. The inequality in point 4 supplies coefficient `a+F₀(c+1)+c+2`, and the definition of LOGSPACE absorbs the remaining simulator constant. |
| T33 | `WordRAM.computesInSpace_of_computes` · 964 | Use T26 in function mode, so the output is exactly `g x` rather than the verdict. The same logarithmic-space calculation as T32 gives one machine and constant for `ComputesInSpace`; no separate polynomial output hypothesis is required for this literal conclusion. |
| T34 | `WordRAM.mem_SPACE_mul_of_decides` · 978 | T25 provides width `c·S` with width-computation space `a·S`, and T31 needs no control on the resulting time bound. Using `S≥logSpace≥1`, the bracket is bounded by `(a+c²+2c+2)·S²`, yielding the required class. |
| T35 | `WordRAM.mem_NSPACE_of_accepts` · 997 | For each input, use its common all-stream time from `hrun` in T27. That supplies all-branch halting, all-branch space and the exact existential acceptance equivalence, and the stated inequality bounds space by `(A+1)·a·s`. These are the clauses of `FinNDTM.DecidesInSpace`, with its per-input time budget. |
| T36 | `WordRAM.mem_NL_of_accepts` · 1015 | Combine T24 and T35 with constant footprint F₀. The same coefficient as T32 bounds the space bracket, establishing NL without imposing an additional polynomial time hypothesis on the RAM program. |

### NDSlice: both theorems

| ID | Declaration · line | Argument |
|---|---|---|
| T37 | `Turing.NDTM.runWith_eq_fixChoice_runFrom` · 61 | Induct on the choice list, with the configuration generalized. If halted, both steps fix it; otherwise the j=0 hypothesis equates the chosen transition with the fixed one, and the remaining hypothesis shifts one time step. Empty lists are immediate, and equality at the endpoint requires no hypothesis about its next transition. |
| T38 | `Turing.NDTM.spaceUsedWith_eq_fixChoice_spaceUsed` · 86 | Apply T37 to every prefix `w.take j` with j≤length w; the restricted agreement premise follows from the original one. The prefix endpoint positions therefore define the same visited set on each work tape, and summing their cardinalities gives equal space. |

### LanguageExtensions: all 27 theorems

| ID | Declaration · line | Argument |
|---|---|---|
| T39 | `Light.XExec.append` · 195 | Induct on the execution derivation. Appending procedure bodies preserves every existing successful lookup and changes no expression or instruction rule, so all state/log/cost indices are retained. |
| T40 | `Light.XExec.loc_eq_of_notMem_assigns` · 204 | Induct on the derivation, using nonmembership in concatenated assignment lists for sequential and branching cases. Each new assignment changes only its named local, emit changes none, and a call updates only its caller result local. |
| T41 | `Light.XExec.bounded` · 216 | The old cases use expression safety and initial boundedness, with the induction hypotheses at intermediate states. Input and coin produce only 0 or 1, bounded by the new premise; halving has absolute value at most that of its operand even for a negative odd integer. Thus state boundedness is preserved, whereas F3 shows why the new premise cannot simply be omitted. |
| T42 | `Light.XExec.mem_outside` · 225 | Only a store can change language memory, and its `Addr` premise places the target strictly below `lim.space`. Induction through sequence, loops and calls preserves equality at every address at or above that boundary; all four new statements leave language memory unchanged. |
| T43 | `Light.XExec.coins_length_le` · 272 | Each coin contributes one bit and costs one. Logs concatenate exactly where costs add, while every other rule has nonnegative overhead, so induction bounds consumed length by total cost. |
| T44 | `Light.XExec.output_length_le` · 278 | Each emit contributes one bit and costs its expression cost plus one, hence at least one. Additivity of output lengths and costs through the compound rules gives the result by induction. |
| T45 | `Light.XExec.det` · 290 | Induct on one derivation and invert the other, using identical guards, expression values, body lookup and initial state to align the rules. Two coin logs that are prefixes of one stream agree at the next consumed bit; after equal prefix executions the remaining logs are prefixes of the same dropped stream. This gives equality of intermediate and final states, both logs and total cost, including terminating loops. |
| T46 | `Light.XExec.io_eq_nil_of_ioFree` · 312 | Induct on the execution, excluding emit and coin through the syntactic premise. At a call, successful lookup makes the body a member of P, so the program-wide premise supplies the needed IOFree fact and both concatenated logs stay empty. |
| T47 | `Light.EndsIO.toXEnds` · 335 | Unpack the `EndsIO` witness and forget its prefix condition and exposed logs. Apply the supplied postcondition implication to obtain the state-only property, keeping the same execution and cost bound. |
| T48 | `Light.EndsIO.mono` · 342 | Retain the execution, logs and stream-prefix witness. Weaken the cost inequality and apply the postcondition implication to the same endpoint. |
| T49 | `Light.EndsIO.of_xEnds_ioFree` · 353 | Apply T46 to the witnessing execution of `XEnds` to show both logs are empty. The empty consumed list is a prefix of every supplied stream, giving the stated `EndsIO` postcondition. |
| T50 | `Light.EndsIO.skip` · 361 | Use the skip derivation with unchanged state, empty logs and zero cost. Zero is below every natural budget and the empty log prefixes every stream. |
| T51 | `Light.EndsIO.set` · 367 | The safe assignment constructor produces exactly the specified local update with no logs. The explicit cost inequality and empty-prefix fact supply the remaining `EndsIO` clauses. |
| T52 | `Light.EndsIO.store` · 376 | The safety and address premises permit the store constructor, with the specified memory update and cost. The output and coin logs are empty, so the stream condition and postcondition are exactly those assumed. |
| T53 | `Light.EndsIO.seq` · 387 | Choose the first execution and then the second execution supplied for its endpoint, using the stream with the first consumed prefix dropped. Concatenating their consumed words gives a prefix of the original stream, while concatenating outputs and adding the two cost bounds establishes the conclusion. |
| T54 | `Light.EndsIO.ite` · 396 | Split on the guard truth value and use the corresponding supplied branch execution. The safe test adds its exact overhead but consumes/emits no bits, preserving the branch's stream-prefix condition. |
| T55 | `Light.EndsIO.whileStep` · 404 | Compose the supplied body execution with the supplied recursive loop execution under the dropped stream, exactly as for T53. The true-test constructor adds the guard overhead and concatenates both logs, giving the displayed cost and postcondition. |
| T56 | `Light.EndsIO.whileDone` · 415 | Apply the false-test execution rule to the initial state, producing empty logs and no body iteration. Its cost is the guard cost plus one, which the given inequality puts within T. |
| T57 | `Light.EndsIO.call` · 422 | The lookup, argument-safety and depth premises permit the call constructor around the supplied callee execution. That constructor restores the caller locals except for the result, preserves the callee memory/logs, and adds exactly argument cost plus two, so the postcondition and budget follow. |
| T58 | `Light.EndsIO.inBit` · 433 | Apply the safe input-bit constructor with its specified integer value and cost. It emits and consumes nothing, so its prefix condition is automatic and the supplied postcondition applies. |
| T59 | `Light.EndsIO.emit` · 442 | Apply the emit constructor, leaving state fixed and appending the singleton nonzero test. It consumes no coins, and the given inequality covers its expression cost plus one. |
| T60 | `Light.EndsIO.coin` · 449 | The supplied decomposition of the stream makes the singleton chosen bit a valid prefix. Use the corresponding coin constructor, its one-unit cost and the assumed postcondition of the local update. |
| T61 | `Light.EndsIO.half` · 458 | The safe-expression premise permits the halving constructor with integer division by positive two. Its empty logs and explicit cost bound give the `EndsIO` witness, including the stated floor behavior on negative operands. |
| T62 | `Light.XEnds.coin` · 467 | Choose the constructor for the Boolean supplied to this theorem and hide its singleton consumed log existentially. The one-step budget and supplied state postcondition give `XEnds`; this proves existence, not a guarantee for every external stream. |
| T63 | `Light.EndsIO.callLast` · 490 | Unpack the `MeetsIO` body lookup and execution specification, and substitute the stated argument values. Apply T57, then translate the callee return/memory specification to the restored caller state through the supplied postcondition implication. |
| T64 | `Light.XExec.ofExec` · 544 | Induct on the old execution and translate every syntax node and successful procedure lookup through `XStmt.ofStmt` and list mapping. No new I/O constructor is introduced, so both logs remain empty and the old state/cost indices are unchanged. |
| T65 | `Light.EndsIO.ofEnds` · 557 | Translate the witnessing old execution with T64. Its empty coin log prefixes any stream, and the original state predicate plus the two empty-log equalities is precisely the required postcondition. |

## Adversarial instantiations

The following are concrete mathematical instantiations of the definitions, in addition to inspection of the 39 supplied Lean examples. They were not independently kernel-checked in this environment. A program displayed as a list uses the extended wrapper for its old instructions.

| # | Instantiation | Result and what it tests |
|---|---|---|
| A1 | Empty input; program `[accept]`; arbitrary W; t=1, f=0 | Choose prefix length 0 and empty footprint: `HaltsWithin` holds with true verdict and empty output. No program can satisfy the predicate with t=0, since no natural n is strictly below zero. Thus zero time is not an accidental acceptance case, while zero touched cells is legitimate. |
| A2 | Empty program; arbitrary input/width; t=1, f=0 | Default fetch rejects immediately with an empty footprint. It cannot accept at any budget because of deterministic rejection, checking the off-program convention. |
| A3 | W=0; `[coin 0, emit 0, accept]`; stream `[true]`; t=3, f=1 | The written W-bit numeral 1 is zero, so the emitted bit is false and the verdict true. This is a genuine degenerate word algebra, not a counterexample: no theorem identifies its true encoding with integer 1 or promises a useful compiler at W=0. |
| A4 | W=1; `[coin 0, bltz 0 3, reject, accept]` | A true coin writes the signed value −1 and accepts; a false coin rejects. Both paths use at most three counted steps and one touched cell, confirming signed branch semantics and why a tiny-width RAM is not the integer language without a fit argument. |
| A5 | W=8; `[one (2^100), emit (2^100), accept]`; t=3, f=1 | This emits true while touching one enormous immediate address. Its address takes more than W bits, but that fixed width belongs to the program-dependent constant; there is no contradiction to `f(W+1)`. |
| A6 | W=8; one instruction `store (-4) (-5)` with cells −4 and −5 holding −7 and 9 | It reads −4 and −5 and writes −7, so the touched set is exactly those three cells. If the pointed-to address aliases a named operand, cardinality decreases; no hidden fourth access occurs. A corresponding load includes both its pointer register and the pointed-to cell. |
| A7 | W=8; input `[true,false]`; input-index values −1, 0, 2 | The reads produce 0, 1, 0. Encoding 128 as a W-bit signed word produces −128, so that value is a negative index rather than an attempt to seek to positive 128. |
| A8 | W=8; source values −3 and 5 in `half` | Arithmetic right shift gives −2 and 2. Integer language division by positive two gives the same floors, excluding the tempting but wrong truncation-to-zero interpretation. |
| A9 | An extended program whose first instruction is `rdIn 0 1` | Its projection immediately rejects, while its actual extended step continues. This invalidates an unrestricted projection-equivalence claim, but not T4/T14: a positive-length continuing projected run does not exist at this position. |
| A10 | Caller q=0, frame width F=2, stack bound Q=10 | The nested callee starts at frame index 3, and its return slot has index 2. Slot 2 is absent from `Stack 3 10` but present in `Stack 0 10`; charging the epilogue to the calling statement gives the required containment. |
| A11 | W=8; `[coin 0, one 1, sub 2 0 1, bltz 2 0, accept]` | Stream `[true]` accepts in five steps; the empty stream repeatedly supplies false and loops. Existential acceptance alone therefore cannot satisfy `exists_ndSimulation`'s hypothesis, as intended; the bad branch defeats the required common all-stream bound. |
| A12 | One language coin assignment, first under `[]`, then under `[false]` and `[true]` | No `EndsIO` execution exists for the empty stream, whereas the other two streams give the respective distinct local values. Those distinct consumed singleton lists cannot both prefix one common stream, so this is not a counterexample to `XExec.det`; the RAM's empty-stream false default is a genuinely different convention. |
| A13 | `lim.word=0`, input `[]`, zero state; a true language coin | A valid one-cost `XExec` writes local value 1, breaking the zero bound. W=8, space=N=Q=0 makes `XFits` satisfiable, so this also concretely tests and confirms F3. With the stated premise `1≤lim.word`, the boundedness theorem survives. |
| A14 | Language program with sole body `coin 0`; input `[]`, word bound 1, depth 1, zero memory/auxiliary argument; outer-call budget T=5 | The call's two variable arguments cost 2, call overhead costs 2, and the coin costs 1. `acceptProb` is 0 with m=0 and 1/2 with m=1 or m=5; `AcceptsND` holds by a length-5 stream beginning true. This distinguishes exhaustion from padding and checks the outer-call costs. |
| A15 | NDSlice with w empty, or with an already halted configuration; also k=0 | Empty-list runs are identical, and halted configurations are fixed for every choice list. Space includes each existing work head's initial position; it is zero for k=0, so no hidden positive-tape assumption is needed. |
| A16 | A two-state slice: both transitions agree at state s0 and move to s1; the transitions differ at s1; choose a one-bit w | The hypothesis is satisfied because it only tests time 0, and both runs end at s1 with equal tape positions. Agreement at time 1 would be unnecessarily strong: the differing next transition has not yet occurred. |
| A17 | Polynomial degree d=0; nonempty constant time budget; or n=0 in a space grade | The P bound uses degree `3d+1=1`, so startup input scanning is still covered. The logarithmic-word specialization promotes d to at least 1, and `logSpace 0=1` supplies every constant-space allowance; a constructible S cannot be zero there. |
| A18 | `[accept, coin 100]`, with the coin unreachable | The program is not `CoinFree`, yet its actual verdict/output are independent of the stream. This confirms that the syntactic predicate is sufficient rather than necessary and does not trivialize its stream-independence theorem. |

None of these instantiations refutes a proposed theorem. A13 refutes a tempting inference needed by an insufficiently specified future compiler edit; A9 and A12 refute stronger equivalences that the actual statements correctly avoid.

## Additional machine-checkable sanity statements worth adding

These are recommendations for the fill/fidelity suite, not additional assumptions for this gate. They target the boundaries not settled by the present executable examples.

1. **Tiny-width encoding.** Prove `coinWord 0 true = 0`, signed `coinWord 1 true = −1`, and signed `coinWord W true = 1` under `2≤W`. Add W=0 input/emit and W=1 branch probes like A3/A4.
2. **Halving agreement.** For every W-bit value, prove that the signed value after arithmetic shift by one equals its signed integer value divided by two. This directly connects the RAM and language operations, including negative odd operands and width zero.
3. **Finite-stream reduction.** For a fixed time budget t, prove that behavior through that budget depends only on the first t coin bits, with explicit false completion for shorter RAM streams. Derive that checking all length-t streams suffices for the RAM all-stream boundedness hypothesis.
4. **Language padding and probability.** Use `coins_length_le` to show that any execution of cost at most T admits a realizing stream of length T. Prove stability of `acceptProb` when increasing m beyond T, rather than leaving that important interpretation solely in prose.
5. **Positive-bound integration.** Include the A13 counterexample as a negative control for any attempted implication `XFits → 1≤lim.word`, and a positive test of whichever compiler invariant supplies this premise after the edit.
6. **Intermediate footprint protection.** Add the extended analogue of `StepsIn.agreeOutside`, then use a nested-call probe where the return slot lies below the callee frame but within the caller footprint. Include a load from a zero-valued cell to distinguish touched-cell accounting from nonzero support.
7. **Mixed-code and purity reuse.** State the extended code-at relation and base-segment lift used by the edited compiler. Add `EndsIO.append` and test lifting a pure library prefix before appending a coin-bearing main routine.
8. **Slice boundary.** Formalize A16 with a choice state exactly at the endpoint, and verify both run and visited-space equalities. This guards against accidentally changing `< length` into an unnecessarily restrictive endpoint hypothesis.
9. **Final landing check.** Build the actual installed import graph after appending B1/B2, including generated constructors/projections and the new facade imports. This checks a different property from elaborating the bootstrap closures over the old snapshot.

## Gate disposition and limits

The four minors are accounting/attribution/screen-scope defects and an explicit future integration obligation. They neither supply a counterexample to a proposed theorem nor reveal an unacknowledged copied-proof family. Therefore **zero blockers and zero majors** is the result of this round, meeting the pack's stated statement-gate criterion.

Carry F3 and the specified mixed-code, stream-padding and footprint obligations into PROG-2's own fidelity and statement checks. Proof completion must discharge the constructive contracts identified here; the attached elaboration log is not evidence that any of the 65 sorries has been proved.

## Notation glossary

- `n`: input-list length; W: RAM word width in bits; t: RAM time budget including the verdict step; f: upper bound on the number of distinct touched RAM cells.
- `TW`, `SW`: time and visited-work-space bounds for computing the width; A: a fixed simulator overhead constant; c, C, a: fixed natural coefficients, local to the claim where they occur.
- `F₀`: a fixed RAM-cell bound; d: a polynomial degree; S: a space-constructible bound; `logSpace n`: the repository's positive binary-logarithmic bound, equal to 1 at n=0.
- K: a set of RAM addresses; q: a compiler frame index; F: its frame width; Q: its stack bound; k: number of work tapes when discussing Turing machines.
- `ρ`: an available RAM/language coin stream; r: the language execution's consumed prefix; w: a sequence selecting NDTM transitions; o: emitted output; v: terminal Boolean verdict.
- `σ`, `μ`: language state and language memory; P: a fixed RAM or language program, as determined by its declaration; L: a language; g: an output function.
- `O(·)`: an upper bound up to a fixed multiplicative constant; `O_P(·)` permits dependence on the fixed program P; “signed W-bit address” means an integer obtained by `BitVec W.toInt`.
- “Internal configuration”: the machine state, input-head position, work-tape contents and work-head positions, excluding the append-only output that transitions cannot read.

