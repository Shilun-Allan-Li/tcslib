SHA-256: `3b9b166e4b282a7c84026a92472dd7b868f6c19323390ae4aac1bcbbe6219bfc`.

Exactly **28 sections** match `## ===== <path> =====`. Both checks match the kickoff.

**H2-S verdict: gate remains open — 0 blockers, 3 majors, 5 minors.** I found no false copied contract and independently reproduced the declaration fidelity checks. The main objections concern the advertised consumer interface and missing evidence. They do not require changing the seven copied contracts or their machines.

This report audits the supplied bundle. I independently checked its bytes, declarations, move, negative control, and log contents. I did **not** independently run Lean: this workspace has neither a Lean executable nor the complete pinned project/dependencies. Kernel-checking results below are therefore attributed to the attached logs, not represented as a fresh replay. Locations refer to the named bundled files; source line numbers disregard enclosing Markdown code fences.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `StepBlockDraft.lean.txt` · `roundTM_iterate`; `H2-design.md` §2.5, O6 | The iteration corollary supplies U-1's divergence-preserving converse. | It exposes only `T ≤ t * B`, with no lower bound or cofinality condition. For a stationary, silent, one-state source self-loop, `T = 0` satisfies every conjunct for every `t`: the source configuration and represented endpoint are unchanged. Thus the stated witnesses need not cover arbitrarily late physical times. This is an inadequacy of the advertised interface, not a false theorem. The attached `UniversalInterpreter.universal_block_run` explicitly includes the missing lower bound. | Add `t ≤ T` to this **additive** result, or supply a separate cofinality theorem. The induction already has positive round lengths available. Keep the copied `roundTM_effect` unchanged. Alternatively, withdraw the claim that this corollary supplies the converse and name the additional positive-block proof obligation. |
| 2 | major | `H2-design.md` §§1.4, 2.3, O11 · H5 | Every input device must transport a native-input machine in lockstep, as Z1 does. | Z1's attached `vhostEmitTM_step` and `runFrom` mean one physical host step per source step. RD-3's proposed SU device stores the position as a binary word and updates it through increment/decrement routines. In that representation, incrementing `011` to `100` changes three cells of one tape; one TM transition can write only one cell on that tape. Arbitrarily long carries require multiple steps. The proposed requirement does not fit this named consumer. | Give H5 a positive, finite **block simulation**, with intermediate frames, output, exit cuts and head envelopes. Retain literal lockstep as a special case for Z1/native devices. State separate resource guarantees: SU needs the logarithmic space ledger, whereas C1/U-1 need a device preserving their time bounds. If “lockstep” was intended to mean correspondence only at checkpoints, say so and specify that weaker interface. |
| 3 | major | `H2-design.md` §§2.5, 3.3, 4.5–4.6 · evidence inventory | The bundle supplies every cited consumer file and supports the requested checks of the frozen constants, contract structure and replay closure. | Section 4.6 promises `UniversalBlock.lean`, `UniversalStartup.lean`, `ClassNP/TMSAT.lean` and the MIG-0a `Contract` draft; none is among the 28 sections. `Universal.lean` refers to `universalBlockBound` but does not define it. Consequently the displayed coefficient and TMSAT comparison cannot be checked against their actual definitions. The exact eight-module closure also lacks the full import graph or attached dependency-scan output. The design document's summaries are not those source definitions. | Supply snapshot-consistent source excerpts or files for these checks, and the import/dependency manifest. Correct the inventory. Distinguish the move-probe check already reported from the full H2-M replay still to be performed. No fresh H2-M replay is demanded at this statement gate. |
| 4 | minor | `StepBlockDraft.lean.txt` · `summaryEmit_none`, `Rep`; `H2-design.md` §§2.3, 2.5 | Blanking and forwarding can be composed using the stated representation and iteration results without another invariant. | After a source output `[true]`, `Rep` requires `some true` at summary cell zero. Blanking that cell destroys `Rep tr c d` for the actual cumulative-output configuration. Also, `roundTM_iterate` concerns the silent `roundTM`, not the wrapper that resets and forwards. The proposed route is nevertheless valid after a small change of simulation invariant, detailed below. | Relate each reset seam to `{c with output := []}` and track the real cumulative output separately in the host's physical output or buffer. Prove reset/forward preservation, including the halting round, and transport the space ledger through that wrapper. Record this obligation explicitly; no emission-mode change to H2 is needed. |
| 5 | minor | `H2-design.md` §4.3 and O2 · ownership manifest | O2 lists all regions touched by the promotion. | Its “only” list omits the new import. The `summaryClock` family at source lines 2000–2038 also needs public-name resolution under §4.3: an `open StepBlock` can preserve its text, whereas the offered qualified-name alternative changes this omitted region. The manifest should specify which approach is used. With two continuations already in flight, new H1 assembly may also reference the private names being deleted. | Use a declaration-based manifest including imports, the namespace opening or summary-clock qualifications, status text and any delivered H1 references. Interpret “between continuations” as a coordinated integration window, not deletion beneath an active H1 worker. The canonizer may continue under a genuinely disjoint declaration carve-out. Recompute the move comparison against the actual integration base. |
| 6 | minor | `fidelity.py.txt` · result handling and coverage | The script is ready to serve as the freeze-check basis. | The announced mutations are detected, but the process still exits successfully when it prints `DIFFER`. It also labels every unmapped draft declaration `ADDITIVE` without checking the five-name additive whitelist or asserting the expected copied inventory. The current bundle passes; the issue is the proposed automated guard. | Exit nonzero on mismatches, missing/extra copied declarations, duplicate names or unexpected additions. Assert the complete expected inventory and whitelist the intended additives before using it as an H2-M gate. |
| 7 | minor | `H2-design.md` §6 · module size | Reporting a roughly 3,350-line single file settles the size-policy question. | `policy.md` §1 calls for splitting a file approaching 1,000 lines unless there is a positive reason not to. The proposal acknowledges that Record/Seek/Round can be split, but gives no reason for retaining all three in a file over three times that threshold. | Propose that split, or record an explicit temporary justification and resolution point—for example, preserving private cross-phase dependencies during this mechanical move, followed by a specified migration window. The Build home and `Turing.StepBlock` namespace themselves are appropriate. |
| 8 | minor | `StepBlockDraft.lean.txt`, `H2-design.md`, `h2-promotion-pack.md` · descriptive accuracy | Several summaries precisely describe the attached code and evidence. | The round bound depends on the table, hence indirectly on `k`, `n` and its contents; only coefficient 50 is uniform. `Key` has 15 constructors but **20 values**, because five constructors carry a Boolean. The reported **101** overlength lines count UTF-8 bytes: the moved source has **83** lines over 100 Unicode characters and the renamed probe has **75**; the draft has zero. The pack's unqualified “axiom prints use at most the standard three” overlooks the two draft corollaries whose displayed prints include `sorryAx`. The additive-section introduction says “three” before four results. | Correct the descriptions, label the line-length metric, and qualify the draft's axiom claim exactly as its log does. Make the new module's required line wrapping part of the landing criteria, even if broader inherited-linter cleanup remains a separate commit. |
| NF1 | note | Bundle; draft; move probe | **No findings — input identity and copied-code fidelity.** | Independent hash/count checks passed. The supplied script reproduces **58 matches, 0 differences**; changing `recordWidth` and the main round bound gives **56 matches, 2 differences**. A separate comparison of all **121** moved declarations, including proof bodies, gives **121 matches, 0 differences** modulo the injective rename map, comments and whitespace. | None for these bytes. Preserve the same checks at H2-M. |
| NF2 | note | Draft · 41 public definitions; seven copied contracts | **No findings — literal copied statements, finiteness and round interface.** | Definitions and statements agree with their private originals. The main contract has a live source premise, positive duration, both positive-time exit exclusions, the complete represented endpoint, silence through the endpoint, the one-cell mirrored/input envelope and auxiliary return-home clauses. It is nonvacuous at `k = 0`, `n = 0` and empty input. | None; keep the copied contracts unchanged. |
| NF3 | note | Draft · five additive results | **No findings — truth of their literal conclusions.** | All five have proofs in the draft. The visited-cell statements follow from the endpoint envelope and run concatenation. The last two depend on the admitted draft round contract, as their axiom prints disclose. Finding 1 concerns the claimed use of `roundTM_iterate`, not its truth. | Address finding 1 before advertising the stronger consumer conclusion. |
| NF4 | note | `CounterLoop.lean`; `EXPCOM.lean` | **No findings — H1 and EXPCOM consumer fit.** | H1's anchor/escape cut is exactly the round interface required by `counterLoopTM_run_done` and `_escape`, with the symmetric orientation of the exit inequality handled trivially. Positive duration permits choosing the round-time function. EXPCOM's `exists_uniformMachineCode` invokes the one-tape format's canonizer and simulator, not the step block directly. | None at H2-S; H1's startup, assembly and ledger remain its own obligations. |
| NF5 | note | `C1LiftProbe.lean.txt`; `NDCodes.lean`; `NTimeHierarchy.lean` | **No findings — C1's choice-lifted table identity.** | The serializer orders choice, state, input read and work reads exactly as the probe does. Splitting the lifted state range yields the false and true halves. `Fin.castLE` preserves successor values, hence unary successor bits; successors return to the lower half. This works also at `numStates = 0`. | Keep the choice installer, nondeterministic host, branch alignment and amortized clock as separate obligations. Do not describe the table-only identity as equality of the complete serialized headers. |
| NF6 | note | Design §3.3; `machine-library-design.md` §16a | **No findings — classification as a return-or-escape round.** | On the attached description of MIG-0a, a positive first-exit contract with `entry` in its exit set contradicts its time-zero cut. A single-return contract omits the distinct escape. Two exits alone are not a problem for ordinary `Contract`, which allows a set; it is the returning entry that causes the first-exit obstruction. | Use MIG-0b's round adapter. Keep the original theorem available so that its output and input-trajectory information is retained. Exact verification against the missing Contract source is covered by finding 3. |
| NF7 | note | Move plan; imports; namespace; duplication | **No findings — proposed move rather than a retained production copy.** | The probe has exactly the proposed three direct imports. The two layout definitions retain their `Turing` names; the generic run/visited lemmas have the proposed `MultiTapeTM` home. The planned deletion removes the old 121 declarations while retaining H1's four semantic-clock declarations. Draft/probe copies are evidence, not proposed second production implementations. | Verify visibility changes, deletion, facade export and the full downstream closure at H2-M. The private-visibility move probe alone does not certify that final public module. |

The following supporting checks are part of the report.

**Consumer conclusions and open questions.**

| Item | Ruling |
|---|---|
| H1 / EXPCOM | The copied contract suffices. Choosing a time from its existential is legitimate on represented live starts; values outside that domain can be arbitrary. The strict cut makes the first positive exit time unique. |
| B6 `U₀` | The native-input, one-work-tape core is suitable. Add the reset-output invariant from finding 4, final-output forwarding before physical halt, and startup/host space composition. The silent-core iteration lemma is not already a theorem about the emitting wrapper. |
| B6 `SU` | The same core is suitable only with a correctly specified H5 block transport. Z1's buffered device is not a substitute for the required sublinear-space suffix device. |
| C1 | The deterministic table can remain unchanged. The choice installer writes the lifted unary state; deterministic phases must ignore their own nondeterministic choices. The table identity does not prove the alignment or the amortized clock. |
| U-1 | The copied core supports a positive-block construction after the host obligations above. The advertised iteration corollary needs finding 1's repair. The frozen numerical coefficient remains unresolved, and its cited source definitions are missing. |
| O1 | Agree: disambiguate the two uses of “H2.” |
| O2 | Agree with a serialized promotion window and declaration ownership, subject to finding 5. Do not invalidate an in-flight H1 worker's private dependencies. |
| O3 | Accept `StepBlock` as the temporary home of the two layout definitions. Their eventual `CodeFormat` home is cleaner; the exact claimed 8-versus-23 closure counts are not independently verified from this packet. |
| O4 | Accept the existing summary encoding for the move. Track the semantic bridge to `OutSummary`/the record encoding; do not require a representation change in these frozen declarations. The other encoding's implementation is not attached. |
| O5 | A narrower surface would be better. An opaque state type is not the only option: helpers such as `payload`, `applyPayload`, `seekRouterTM`, `seekNext`, `seekPart`, `seekRed`, `part` and `red` need not all be consumer-facing merely because public definition bodies use them. Distinguish types appearing in public signatures from implementation helpers. Keeping the documented 70-name surface temporarily is not a soundness blocker. |
| O6 | Include the additives with the cofinality repair in finding 1. The output wrapper still needs its own invariant. |
| O7 | Agree: a named round-time function can wait. The endpoint cut proves uniqueness, so a `Nat.find`/choice construction causes no ambiguity for admissible starts. |
| O8 | Agree that this does not force a change to the copied contract now. Record the unresolved coefficient obligation. A larger available upper bound does not prove the actual execution time exceeds the old bound. Restating the coefficient or retaining an old timed implementation also revises U-1's recorded requirement to keep statements unchanged and delete the bespoke layers; neither should be treated as an already-approved resolution. |
| O9 | Accept the temporary module placement and `MultiTapeTM` namespace. Moving generic results down later is appropriate; the exact larger closure has not been supplied. |
| O10 | Agree with a separate, replayed style commit after the mechanically checked move. Correct the baseline counts and satisfy the new file's 100-column requirement. |
| O11 | Disagree with literal lockstep as a universal requirement; see finding 2. |
| O12 | The qualification “where they fit” is essential. `recordTM_effect` assumes already-canonical action bits; it is not a validity parser for arbitrary input and executes the payload. F7-1(c) is not resolved just by exporting it. If the canonizer needs only the fixed-prefix walk, expose the appropriate read/frame contract or retain the factoring obligation explicitly. |

**The two logical interface checks, in detail.**

For finding 1, choose a live source whose transition keeps its state, all heads and all tapes fixed and emits nothing. Then, for every source time `t`,

\[
M.\mathrm{runFrom}(c,t)=c.
\]

For any represented entry configuration `d`, the conclusion of `roundTM_iterate` is satisfied by `T = 0`: the endpoint is `d`, its visited sets contain only its starting head cells, and the no-`halt` condition checks only time zero. Consequently the stated upper bound does not establish temporal progress. With the proposed repair, the converse uses

\[
\forall t\;\exists T:\quad t\le T\le tB,
\qquad
\forall u\le T:\quad \mathrm{state}(u)\ne\mathrm{halt}.
\]

For an arbitrary physical horizon `u`, choose `t = u`; then `u ≤ T`, so the no-`halt` clause applies at that horizon. The required lower bound follows by induction: `0 ≤ 0`, and concatenating a round of positive integer duration gives `t + 1 ≤ T + T₁`. This is a statement-level repair justified by the supplied positive-duration contract, not a claim that I kernel-checked a new proof.

For finding 4, start with a source configuration whose output is `[true]`. Its representation forces summary cell zero to contain `some true`; replacing that cell by `none` cannot preserve that representation. The valid round-local replacement is the source configuration `{c with output := []}`. Its input symbol, state and work reads are identical to those of `c`, so the selected action is identical. Applying the unchanged contract to that configuration gives

\[
\mathrm{summaryEmit}(\mathrm{none},a.\mathrm{output})=a.\mathrm{output}.
\]

The wrapper forwards this optional bit exactly once, resets the cell, and re-establishes the empty-output representation for the next source core. Its separate invariant tracks the accumulated real output. Forwarding must precede physical halting on the final round. The reset and forwarding leaves can keep every work head stationary, so they need not enlarge the core's visited sets; their configuration transport and control cuts still need proof.

**Independent definition restatements.** These restatements come from the defining expressions. The private source is the fidelity reference for this promotion; the cited textbook motivates the interpreter, not these exact implementation choices. Public docstrings agree subject to the qualifications below and finding 8. I do not claim an independent comparison against absent textbook pages.

| Proposed public definition | Mathematical meaning and docstring check |
|---|---|
| `workReadsK` | Lists all `k`-tuples of blank/false/true reads, with tape zero outermost; at zero tapes the sole tuple is the empty function. Matches. |
| `tableBitsK` | Concatenates action encodings in state, input-read, then work-read order. Matches. |
| `outputSummary` | Sends the empty output to blank, exactly `[true]` to true, and every other output to false. Matches. |
| `summaryEmit` | Leaves the summary unchanged for no emission; blank followed by true becomes true; every other actual emission makes the summary false. Matches. |
| `recordWidth` | The fixed-field length is `4*k + 4`. Matches. |
| `RecordState` | Either the live exit `none`, or a read count between zero and the fixed width together with a fixed-width Boolean buffer. Matches; the outer configuration option still distinguishes physical halting. |
| `tableTape` | Selects auxiliary tape `k`. Matches. |
| `summaryTape` | Selects auxiliary tape `k + 1`. Matches. |
| `payload` | Parses the fixed bits followed by a dummy halt tag, with state type `Fin 1`; on parse failure returns an idle, silent, halting source action. The docstring's canonical-record restriction is essential; this is a total decoder with a fallback. |
| `applyPayload` | Applies the decoded input and mirrored-work actions, writes the updated summary, leaves auxiliary heads fixed, emits nothing and enters the reader's live exit. Matches. |
| `recordTM` | Reads the fixed-width prefix into control, treating a blank read as false, then applies its payload; its exit idles. The advertised valid-record behavior matches; it is not a validator. |
| `recordFinTM` | Bundles that reader as a finite binary machine on `k + 2` tapes. Matches. |
| `workRank` | Returns the index of the work-read vector in the enumerated list, bounded by `3^k`. Matches. |
| `inputRank` | Assigns ranks zero, one, two to blank, false, true. Matches. |
| `readRank` | Forms `inputRank * 3^k + workRank`, bounded by `3^(k+1)`. Matches. |
| `SuccPhase` | Tag-reading, unary-reading, or one of two live completion states. Matches. |
| `succFieldTM` | Consumes a successor tag; a true tag starts a scan through unary ones and the terminating false. With copying enabled, copies that word to a distinct destination tape; otherwise only the source head advances. Exits idle. The distinct-tape qualification belongs with the public description, as it does in every contract. |
| `succFieldCfg` | Constructs a configuration with a specified state, an optionally overwritten destination interval and the prescribed source/destination head advances. It is a configuration formula, not an unconditional execution theorem; the execution contracts impose distinct tapes. |
| `afterTag` | Preserves all data, advances the source head once and selects unary control. On a halt tag it is only an intermediate algebraic constructor in the endpoint formula, not the actual post-tag control. |
| `SkipPh` | Chooses the reader's control for the first phase and the successor walker's control for the second. Matches. |
| `skipPart` | Chooses the reader or the noncopying successor walker. Matches. |
| `skipRed` | Redirects at the completed fixed-prefix read, before its payload executes. Matches. |
| `recordSkipTM` | Composes those phases to pass a whole action record without executing it. Matches. |
| `SeekCtrl` | Finite router states remember a read rank, a within-group countdown and whether the request is in the final partial group. Matches. |
| `seekRouterTM` | Captures the current read rank, advances to the unary state word, requests one full read-group skip per unary one and then the required rank-prefix skips. Matches on canonical layouts. |
| `seekNext` | Decreases the requested skip countdown or returns to state scanning/completes selection when that countdown ends. Matches. |
| `SeekKey` | Uses `none` for the router and a rank/countdown/final-group triple for a skipper invocation. Matches. |
| `SeekPh` | Assigns router control or skipper control to those keys. Matches. |
| `seekPart` | Selects the router or the whole-record skipper. Matches. |
| `seekRed` | Dispatches each router request to the skipper and each completed skip back to the appropriate router continuation. Matches. |
| `seekTM` | Runs this dispatch network, beginning with observation of the current source reads. Its intended selected-record behavior is conditional on the canonical table/state layout. |
| `twoMoveTM` | Performs exactly two moves of one selected work head in the supplied direction, then idles. All other data and output remain unchanged. Matches. |
| `Key` | Enumerates the round's administrative phases, carrying the live/halt Boolean during restoration. There are 20 keys, from 15 constructors. |
| `Ph` | Assigns each key its component's finite control type; the assignment depends on `k`, not the coded state count. Matches. |
| `part` | Chooses the lookup, catalog scan/clear, fixed move, reader or successor-copy machine for each phase. Matches. |
| `exit` | Returns the entry key for a live successor and the halt key otherwise. Matches; both are live controls. |
| `red` | Routes completed phases in the fixed schedule, starting lookup from entry and returning to the selected exit after restoration; halt has no redirect. Matches. |
| `roundTM` | Instantiates `phaseHostTM` with that schedule and entry state. Matches. |
| `roundFinTM` | Bundles the round as a finite binary machine with `k + 2` tapes. Matches. |
| `summaryCells` | Places the summary at zero and a supplied buffered word beginning at two, leaving cell one and all other out-of-buffer cells blank. It accepts any word; `Rep` specializes it to unary state data. |
| `Rep` | Equates native input positions, all mirrored tapes and heads; fixes the complete canonical table and summary/state tapes; and puts both auxiliary heads at zero. It imposes no block control or physical-output constraint. `roundTM_effect` separately imposes entry, so the design's “control unconstrained” wording applies to `Rep` alone. |

The six named instances supply finiteness and decidable equality for the three dependent phase families. The three inductive controls also generate constructors and deriving declarations; the advertised 70 counts only explicitly named declarations, not every generated environment name. The precise advertised surface is **41 definitions/types, 6 named instances, 23 theorems**. The draft contains 63 of these names; the seven others—`outputSummary_true`, `summaryEmit_other`, the four `summaryCells` lemmas, and `inputPos_runFrom_of_inputTape_eq_zero`—are visible in the source/move probe and included in the full move comparison.

For completeness, the nine moved definitions remaining private have these meanings:

| Private definition | Mathematical meaning |
|---|---|
| `readCfg` | The reader configuration after a specified number of prefix bits: buffer filled below that count, false elsewhere, table head advanced by the count. |
| `seekCfg` | Replaces a live reader control by a specified selector-router control using state mapping; halted configurations remain halted. |
| `seekCost` | Total serialized length of the skipped records plus three steps per record. |
| `seekShift` | Shifts only the table and summary heads by the supplied nonnegative offsets. |
| `readActions` | Lists all actions at a fixed state, grouped by blank/false/true input read and then work reads. |
| `roundData` | Combines a source input/mirrored bank with supplied table and summary words, auxiliary positions and physical-output prefix, at the reader's initial control. |
| `RoundWindow` | Requires each input/mirrored head separately to be at its source start or action endpoint; does not constrain auxiliary heads or synchronize the alternatives. |
| `RoundSpan` | An exact run segment whose strict prefixes, including time zero, are live, avoid both round exits and satisfy `RoundWindow`. This internal segment is not the whole returning round starting at entry. |
| `atKey` | Maps a live reader state to the specified round key/control while preserving all noncontrol fields. |

The C1 probe's additional definition, `liftTr`, selects the false table below `numStates + 1`, the true table above it after subtracting that offset, and embeds every successor into the lower half. Its docstring matches.

**Literal plausibility of each draft admission.** These are checks of statements, boundary conditions and the supplied proof architecture, not an audit of the inherited tactic scripts.

| Contract | Why the literal statement is supported |
|---|---|
| `recordTM_effect` | The fixed prefix takes `4*k + 4` read steps and one execution step. The canonical-bit hypothesis identifies the payload, and the action updates the source fields and summary even on a halting transition. Before execution only the table head moves; the final action moves each mirrored/input head at most one cell. |
| `succFieldTM_run` | A halt field consumes its sole tag and copies no word. A live field consumes its tag and the entire unary successor including the terminating false. Distinct source/destination tapes make the framed copy and both head advances compatible. |
| `succFieldTM_cut` | Before the field length is exhausted, the control is either the initial tag phase or the unary scan. Its completion states occur only after the halt tag or unary terminator is consumed. |
| `succFieldTM_heads` | The source advances at every field step. An enabled destination starts advancing only after the tag, hence its displacement is natural-number `t - 1`; input and physical output are untouched. |
| `recordSkipTM_run` | The reader is intercepted at its fixed-width boundary, before payload execution. One dispatch and the noncopying successor walk give total time `record.length + 1`, table displacement `record.length`, and unchanged remaining data. |
| `recordSkipTM_spec` | Prefixes split into reading, the stationary dispatch, and successor traversal. This gives the stated `min`/truncated-subtraction displacement formula, unchanged tapes/input/output, and no premature completion exit. |
| `roundTM_effect` | The representation supplies a real serialized row for the current live source state and reads. Lookup, state clearing, payload execution, successor installation and restoration produce the represented action endpoint. The positive initial dispatch and internal cuts distinguish the first return from time zero; the source heads move only at the payload and the auxiliary motion is bounded by total round time. |

The five additives have the claimed literal roles: `summaryEmit_none` is a three-case identity; the two generic visited-set inclusions split or shift visiting times; `roundTM_visited` projects the envelope through the two representations; `roundTM_iterate` concatenates live-source rounds and their visited sets. The supplied proofs of the last two invoke the round contract as stated, without invoking its private trace implementation. They do not establish the additional output-wrapper invariant or cofinality omitted from their conclusions.

**Adversarial instantiations.**

| Instantiation | Result |
|---|---|
| `k = 0`, `n = 0`, empty input | There is one source state and one empty work-read vector, with three input-read entries. The auxiliary tapes are still distinct. A halting action has four fixed bits plus its one-bit halt tag: reader time 5, skipper time 6, successor-walker time 1. The main contract remains substantive despite having no mirrored tapes. |
| Halting action emits `some false` or `some true` | The payload still executes and updates the summary before reaching the live `halt` exit. For an empty prior output, the summary equals the emitted bit. A forwarding wrapper must process that cell before terminating. |
| Existing source output `[true]`, then a blanked summary cell | The original `Rep` premise fails, exposing finding 4. Relating to the same source core with empty output repairs the application. |
| Stationary silent self-loop, arbitrary live prefix length | The additive iteration conclusion admits the zero-time witness at every horizon, exposing finding 1. This does not refute the concrete round machine or the copied positive-duration theorem. |
| Empty input at either boundary; mirrored head at a negative integer cell | Input moves are clamped; the two-boundary empty-input case still satisfies the start-or-end envelope. Work-tape positions are integers without a nonnegativity premise, so negative positions do not invalidate the mirrored relation. |
| Nonempty pre-existing physical output prefix | `Rep` permits it and the round's silence clause preserves it at every prefix. Physical output is distinct from the simulated output summary. |
| Malformed table, already-halted source, or coincident successor-copy tapes | The relevant hypotheses deliberately exclude these: exact `tableBitsK`, live source state, and `src ≠ dst`. No validator or already-halted round is being promised. |

Useful permanent sanity results are the lower-bound/cofinality version of iteration; first-positive-exit uniqueness; the reset/forward representation bridge including a final emission; the zero-tape/empty-input instance; and C1's choice-lift action correspondence in addition to its table identity.

For the space claim, the mirrored visited sets are subsets of the source's visited sets. Each auxiliary visits at most `2*B + 1` cells, so the two auxiliaries contribute at most `4*B + 2` tape-cell pairs. With a fixed table this is a per-code constant. Startup and the correctly framed output/input wrappers must then be composed into the consumer's space bound; the draft corollaries alone are not the complete consumer ledger.

**Attestation disposition.**

| Attestation | Check and limitation |
|---|---|
| Draft: zero errors, seven sorry warnings, no other warnings | The attached log has exactly those seven warnings and records exit status zero. The draft has exactly seven comment-stripped `sorry` tokens. I did not independently elaborate it. |
| Maintainer's independent second elaboration | Asserted in the pack; no separately identifiable second-run transcript is supplied. I cannot verify its independence or execution. |
| Draft axiom prints | The nine other displayed entries use subsets of the standard three axioms or no axioms; `roundTM_visited` and `roundTM_iterate` explicitly include `sorryAx`. This agrees with the dependency on the draft contract. The pack's unqualified summary requires finding 8's correction. |
| Fidelity 58/58 | Independently reproduced, including both negative-control mismatches. Finding 6 concerns future automated failure handling. |
| Move: 121 declarations, no residual `h1` identifiers in code | Independently checked declaration coverage, injective renaming and complete normalized bodies. All 121 match. The probe retains private visibility for the originally private declarations, as the design acknowledges. |
| Move: zero errors, zero sorries, 67 inherited warnings | The attached output has zero error diagnostics and 67 warnings; the probe has no `sorry` token. The warning categories match exactly: 41 unused simp arguments, 8 unreachable tactics, 7 sequencing lints, 6 no-op `omega`s, 2 `simpa` suggestions, 2 no-op `congr`s and 1 unused variable. Elaboration success is repository-reported rather than freshly replayed here. |
| Move plus additives: standard axioms, zero errors | The elaboration log reports this and prints seven relevant contracts/corollaries with the standard triple. `MovePlusAdditive.lean` and its full transcript are not separate attachments, so this remains the attached log's assertion. |
| C1 probe: zero errors and warnings | Its source has no admissions, its statement matches the attached serialization, and the elaboration log records an empty diagnostic block with exit status zero. No independent Lean replay is claimed. |
| Eight-module replay closure | The proposed count is arithmetically eight: StepBlock, CodeSimulator, Codes2Tape, EXPCOM, Relativization, two facades and the root. Completeness of that set is not established by the partial attached import graph; see finding 3. The actual final replay is correctly scheduled for H2-M. |
| Duplication and deletion | The proposed move leaves no old production implementation. This does not independently recertify all historical duplication-screen claims in the predecessor report. O4 and F7-1(c) remain explicitly tracked semantic/factoring issues. A final deletion and dependency check belongs to H2-M. |

**Notation:** `B = 50 * ((tableBitsK tr).length + 1)`; `t` is a source-step horizon; `T` and `T₁` are physical durations; `u` is a physical observation time; `state(u)` denotes the block control at that time and `halt` its designated live escape; `c` and `d` are source and block configurations; `a` is the selected source action. Other identifiers retain their bundled definitions.
