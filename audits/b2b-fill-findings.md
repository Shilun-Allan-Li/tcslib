**B2b fill gate — external audit findings**

Audited head: `cef76e00`, `complexity/arora-barak-ch3-4`, after PR #49. Scope: the cumulative B2b change to `TCSlib/Complexity/SpaceComplexity/Inclusions.lean` from `2483ff81`, including the three deliveries, their binding briefs, and P4.1 Question 5. The uploaded bundle contains exactly 70 sections; its SHA-256 is `50ce1a937a31d856d6d18eb038a1182cf1997077913d57aa5fa835d9071dae39`.

No mathematical, statement-freeze, construction-route, or unacknowledged-duplication defect was found. One minor concerns the packet's missing audit standards. The zero-blocker/zero-major gate can close.

I independently checked source and patch consistency, historical source freezes and hashes, contract composition, screen deltas, and the attached evidence. I reran the supplied screen over all 14 files. I did not rerun Lean elaboration, lint, or axiom inspection, and made no repository changes. Kernel execution and object-file provenance remain supported by the supplied execution records.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `b2b-fill-bundle.md` · audit standards | The packet omits the standards needed to apply its requested severity and duplication rules. | None of its 70 sections is `audits/TEMPLATE.md`, `policy.md`, or `workflow.md`. I recovered all three at `cef76e00`; this resolved the omission for this audit. | Record the omission in the resolutions and include these standards in future bundles. Preserve the shipped packet. No Lean change is required. |
| 2 | note | `Inclusions.lean` · `b2b_trial_run`, `b2b_round_run`, `b2b_search_contract` | The continuation's proof restructuring remains within route 1. | Both counted rounds and the final call consume the same trial contract. Only counted rejecting rounds add clear/increment. Classical durations are proof witnesses; the machine definition does not depend on them or on a membership oracle. | None. |
| 3 | note | `Inclusions.lean` · `b2b_callEmb`, `b2b_trialCfg` | The two disclosed in-file screen matches are permissible assembly similarities. | The rerun gives 67/102 characters for the two different selections and 119/184 for the two different configuration records. Neither copies an existing routine or proof. There is no screened cross-file pair involving `Inclusions`. | None; retain the recorded explanations. |
| 4 | note | `Inclusions.lean` · status comments and file size | The maintainer refresh and the file's size are acceptable. | Commit `6da48293` changes two status comments only; stripped code equals delivery 3. The final file has 2,880 lines, four public theorems, 64 named private declarations, and six additional private instances. The brief requires local helpers and explicitly sets no cap. | None. |
| 5 | note | Replay, axiom, integrity and probe records | The records support the claimed completion, with identifiable verification limits. | Public axiom prints and target admission walks agree; the private census checks direct `sorryAx` references. Full archive verification, non-execution of environment helpers, and fresh-olean creation cannot be independently established from the supplied summaries alone. | None; retain the distinction between reproduced checks and execution attestations. |

**1. Freeze.** The attached base has Git blob `a6ddd65c5ad952bebd0d1ad4292752b91d80706d`. Applying the cumulative patch in memory reproduces the attached head exactly, with blob `f76074f2d844125d4cdb3eae83222cb9ef3c9375`; that is also the blob returned for the [pinned repository file](https://github.com/Shilun-Allan-Li/tcslib/blob/cef76e00/TCSlib/Complexity/SpaceComplexity/Inclusions.lean).

All four public signatures are byte-identical. The complete declarations `DTIME_subset_SPACE` and `P_subset_PSPACE` are byte-identical. Only the two target public bodies change. The five added imports are exactly `Build.CounterLoop`, `Build.VirtualInput`, `Build.Seam`, `Machines.Clean`, and `CircuitComplexity.MeyerTableau`, under the sanctioned-import comment. There are no added admission, unsafe-execution, or extra-axiom tokens.

The four removed lines are precisely the old module status, the old closing line of the extended NP docstring, and the two `sorry` lines. Historical snapshots independently confirm that delivery 2 changes only `b2b_host_contract` among existing declarations and adds ten privates; delivery 3 changes only `b2b_search_contract` and adds eleven. Neither changes its helper's statement or the already landed machine.

**2. Route fidelity.** Steps A–C obtain the verifier through `P_subset_PSPACE`, clean it through `LogProg.cleanTM_run`, and reserve the prescribed word tapes and three doubled banks. Steps D–F build the shared test, rejecting suffix, setup, counted loop, final test, and answer phases using the prescribed public rows. Dispatch uses `phaseHostTM`; the two R2 seams occur inside `b2b_hostedSource`, exactly where the brief permits them.

There are exactly four new primitive transition-table families: rewind, verdict reader, anchor, and answer emitter. They use `controlAction`, `tapeAction`, `inputMoveAction`, and `emitAction`. The supplied probe covers the rewind, virtual rewind, verdict reader, anchor/type assembly, and the public emission interface; the delivered glue contracts establish the actual uses. No other primitive machine or dispatch combinator is introduced.

The one-definition rules hold: one `b2b_testTM`, one `b2b_trial_run` shared by `b2b_round_run` and `b2b_finish_last`, one rejecting round wrapper, one `b2b_rewindTM` with the five prescribed construction sites, and one polynomial ledger. The final certificate has no successor, so sharing the trial while keeping clear/increment in the counted-round wrapper is the correct factorization. `b2b_setup_run` merely packages the existing five setup phases. The duration function is well-defined using certificate-configuration injectivity and `Meyer.ctrVal_enumWord`; it does not alter the finite controller.

Steps H–I are discharged by the fixed-window composition and the exact witness equivalence below. Neither R8.8 (`seamCompTM₂_run_ofCfg`) nor R8.5e (`exists_inputCallTM`) is cited. The alternative L row is not used.

**3. Question 5: all five obligations are discharged.**

| Obligation | Source evidence and ruling |
|---|---|
| 1. Exact width, complete enumeration, overflow, zero width | `b2b_setup_run` starts with certificate `replicate Q false` and counter `replicate Q true`. `b2b_counter_value` gives counter value `2^Q - 1`. `b2b_round_run` and the orbit invariant in `b2b_search_contract` test `enumWord Q r` in order. `Meyer.incFixed_enumWord` supplies a successful successor for each counted round. The setup's overflow creates the initial zeros; count exhaustion determines the final call. `b2b_verifies_iff`, using Meyer's length and inverse-value lemmas, proves completeness. Early acceptance stops the search; otherwise there are exactly `2^Q - 1` counted calls and one final call. |
| 2. Preserve input/certificate; simulate exactly the concatenation | `b2b_trial_capture` copies the native input, and `b2b_trial_copy` with `b2b_buffer_concat` identifies the entire buffer as `bufferTape (x ++ u)`, including its blank exterior. `b2b_trial_call` invokes the public virtual-input lockstep with the proper boundary tag. Its endpoint preserves the certificate and buffer, restores the buffer head, and leaves the native input head at one. The underlying input is read-only. |
| 3. Internal capture and one physical decision bit | The verifier call uses `embedSilentRetTM` into CAP. `b2b_trial_run` explicitly proves empty physical output at every prefix. Canonical round endpoints also have empty output; monotonicity of append-only output excludes an earlier emission on a round ending with empty output. The counter's administrative steps are silent. `b2b_finish_answer` supplies exactly one bit; `b2b_finish_last` and `b2b_search_contract` preserve that singleton result. |
| 4. Reset before reuse, with no accumulated history | The clean-call contract blanks both verifier banks and resets their heads. `b2b_trial_verdict` reads and erases CAP, returning its head to zero. `b2b_reject_suffix` clears BUF and increments the fixed-width certificate. The exact rejecting endpoint of `b2b_round_run` has blank scratch, origin work heads, native head one, and empty output. Each next call starts from that same shape. |
| 5. Fixed polynomial windows for all calls and resets | `b2b_trial_run` and `b2b_round_run` bound every prefix head by `n + Q + cV*((n+Q)^e+1) + cI + 1`. Both branches of `b2b_search_contract` use the counter-loop contract's third clause for the counter interval and fourth clause for body heads. The final-call embedding frames the counter; dispatch and answer preserve heads. `b2b_host_contract` includes setup in one common radius and converts the visited-set containment to a total cardinality bound. |

For clarity, using the constants already in the source, the complete-run calculation is

\[
\begin{aligned}
n&=|x|,& Q&=C(n+1)^c,\\
K&=4+2M_V.k+2M_I.k+2M_P.k,\\
W&=n+Q+c_V((n+Q)^e+1)+c_I+c_P(n+1)+1,\\
\forall t\le T,\ \forall j<K:\quad |\operatorname{head}_j(t)|&\le W,\\
\operatorname{visited}_j(T)&\subseteq[-W,W]\cap\mathbb Z,\\
\operatorname{spaceUsed}(T)
&=\sum_{j<K}|\operatorname{visited}_j(T)|\\
&\le K(2W+1)\\
&\le D(n+1)^f\\
&\le D\,2^f(n^f+1),\qquad f=(c+1)(e+1).
\end{aligned}
\]

The last two inequalities are `b2b_ledger_bound` and `b2b_mem_PSPACE_of_ledger`. All constants and the machine are chosen before the input. No factor counts trials. The sole occurrence of `spaceUsed_le_mul_succ` in the file is inside the unchanged `DTIME_subset_SPACE`; it is used to obtain the verifier's polynomial space bound, never to bound the whole search by its running time.

The correctness equivalence is

\[
\begin{aligned}
\text{host accepts }x
&\iff\exists r\le 2^Q-1:\ x++\operatorname{enumWord}(Q,r)\in V\\
&\iff\exists u:\ |u|=Q\ \land\ x++u\in V\\
&\iff x\in L.
\end{aligned}
\]

The accepting branch uses the least accepting counted index. If no counted word accepts, the equivalence reduces to the last word's verdict. Meyer's identity `ctrVal (enumWord Q r) = r` below `2^Q` also makes the enumeration injective, so it repeats no candidate. Halting follows from the exact finite round durations and the final-call contract, without requiring a polynomial cleanup time.

The following adversarial cases are covered by the literal contracts, not separate executed Lean tests:

| Case | Consequence |
|---|---|
| `C = 0` | `Q = 0`, hence `2^Q - 1 = 0`: no counted trial; the continuation tests `[]` once, on virtual input `x`. |
| Empty input with `C > 0` | `Q = C*(0+1)^c = C`; positive-width certificates are still enumerated. |
| Only the all-true word verifies | Every counted trial rejects; the final call accepts. This checks the upper endpoint excluded from the counted rounds. |
| No certificate verifies | All candidates are exhausted and exactly `[false]` is emitted. |
| Empty virtual input or zero verifier work tapes | Virtual positions still have both boundary positions; the buffer interval is `[-1,0]` when empty. Zero-sized payload banks cause no invalid tape selection; the host retains its word and counter tapes. |

**4. P4.1 notes.** Note 8 is satisfied by actual trajectory/frame contracts: clean-call radii, R1/R1′ projections and frames, R2 visited-set containment, the phase-host prefix equality, framed catalog rows, and Z1's buffer/bank clauses. Equal per-call cardinality estimates are not substituted for fixed origins. Note 9 is satisfied: `SAT3_mem_PSPACE` is exactly `NP_subset_PSPACE SAT3_mem_NP`, and its docstring explicitly limits the claim to polynomial space. It adds no parser or linear-space claim.

**5. Combined tree.** `fills-3-combined-replay.log` contains 13 module entries, each with exit 0 and zero errors; `Inclusions` has zero admission warnings. The other reported warnings belong to the declared unfinished modules. The log identifies `63c7c4ed` as the checked combined tree. A read-only [comparison to `cef76e00`](https://github.com/Shilun-Allan-Li/tcslib/compare/63c7c4ed...cef76e00) independently shows no changed Lean source. Thus the replay is relevant to the audited head despite its earlier commit identifier. The public Bool counter-loop contracts used by the search retain the required trajectory clauses after the generic generalization.

The axiom log records identical outputs on the per-fill and combined trees: all four publics use only `propext`, `Classical.choice`, and `Quot.sound`, and both target closure walks are empty. The probe source walks constant dependencies; it does not merely search source text. Its 474-constant private census checks direct references, which should not be confused with an independent transitive axiom print of every private constant. The target closure walks provide the relevant transitive admission check for this gate.

**6. Duplication.** The exact supplied script was rerun over the exact prescribed 14-file population. Its output matches every line of `screen-combined.txt` after removing the bundle's extra separator newline:

| Stage | Screened declarations | Pairs | Reproduced characters |
|---|---:|---:|---:|
| Corrected pre-delivery-1 baseline | 784 | 626 | 173,944 |
| After delivery 1 | 817 | 627 | 174,011 |
| Continuation baseline after intervening fills | 843 | 634 | 177,277 |
| After delivery 2 | 854 | 634 | 177,277 |
| After delivery 3 | 865 | 635 | 177,396 |
| Audited combined tree; independently rerun | 869 | 639 | 178,704 |

The historical `b2b-screen-base.txt` is the narrower 665/458 run; the integration record already corrects this, and the continuations use the corrected baseline. The intervening changed pair lines concern Catalog. The final four additions are exactly the two directions of `counterLoopTM`/`counterLoopTMVia` and the two directions of the Bool done/escape wrapper pair. The [pinned R8.0b resolutions](https://github.com/Shilun-Allan-Li/tcslib/blob/cef76e00/audits/s12-8-fill-D-resolutions.md) confirm the definition-pair acknowledgment and scheduled `R80B-E1` resolution; the wrappers use the accepted Z5 pattern. This audit does not expand that acknowledgment.

The two `Inclusions` pairs are exactly those in finding 3. Source inspection also finds no copied/adapted EXP enumerator, second counter or loop host, private virtual-input simulation, rewind induction, generic first-halt or halt-to-live replacement, or generic visited-interval lemma. The local orbit induction instantiates the prescribed counter loop using Meyer's arithmetic. Rewind and first halt cite their public results. Specialized composition/liveness facts are not substitute implementations of those routines. No B2b duplication debt requiring a new human acknowledgment was found.

**7. Documentation.** The fill appendix accurately names the counter loop, phase dispatch, cleanup, copied buffer, and final-word continuation. The module's proved tag is supported by the target axiom evidence. The private sketches describe the delivered decomposition and fixed windows. The two stale private status paragraphs are corrected accurately by `6da48293`; independent comparison confirms identical comment-stripped code. Ground rule 3 constrains fill-agent edits; the disclosed maintainer synchronization does not weaken a statement or change a proof, and is acceptable.

**8. Size.** I do not disagree with the recorded exception. The 115 → 2,880 line increase is independently confirmed. The reported 64 private declarations are the named-declaration count: 24 definitions, five inductives, and 35 theorems; six private instances are additional. Four public theorems remain. File size alone creates no finding under the explicit brief and the recorded user direction.

**9. Repository-side attestations.**

| Attestation | Verification or qualification |
|---|---|
| Delivery integrity | The manifests contain exactly 25, 50, and 25 entries. Each delivered source, recovered at its integrated commit, matches its manifest SHA-256. The supplied delivery-3 report, sweep, axiom, freeze, admission-inventory, probe, and screen files also match their listed hashes after removing bundle separators. Complete ZIP/bundle/patch verification cannot be rerun from the available subset. |
| Environment shims and scripts | The first two manifests list the disclosed C files; delivery 2 also lists `evidence/check_freeze.py`. Delivery 3 lists no C file or script. Their non-execution during integration remains a maintainer attestation. The fill's Lean source does not invoke them. |
| Freeze | Independently verified cumulatively and across all three integrated source stages, as detailed in item 1. |
| Replays | All three per-fill summaries report four successful modules; the owned-file warning counts are respectively 1, 1, and 0. The combined summary reports 13 successful modules. This audit did not independently recreate their oleans. |
| Agent sweep | The attached final-tail log contains 19 successful modules, zero errors, and 22 unchanged admission warnings outside `Inclusions`. Completion of the earlier 112-module bootstrap is stated in the report; its full log is not attached. |
| Axioms | The maintainer's four public prints and empty walks agree with the delivered result. The agent's 15 prints contain no `sorryAx` or nonstandard axiom. These are inspected outputs, not newly executed prints. |
| Pre-ship probes | The original output, both continuation pre-ship logs, and the final agent probe each contain zero errors, zero admission warnings, and eleven axiom prints within the standard triple. The probe's extra imported unfinished modules do not appear as admitted dependencies of its printed results. |
| Lint | The attached result is 0 FAIL / 2 WARN over 45 files. Both warnings are for size (`Inclusions` and `Logspace/InputAccess`). The 2,879-line figure in that pre-refresh log becomes 2,880 after the verified one-line comment expansion. |

For completeness, the meanings of all newly defined objects, read from their Lean expressions, agree with the route and documentation:

| Definitions / inductives | Meaning |
|---|---|
| `B2bRewindState`, `b2b_rewindTM` | Three control states; scan left to the boundary and return the input head to one. The unused `done` state is stationary. Work heads and output remain fixed. |
| `B2bVerdictState`, `b2b_verdictTM` | Move CAP left once, read and erase the bit, then retain its Boolean value in a live exit state. |
| `b2b_anchorTM`, `b2b_answerTM` | A stationary singleton anchor and a two-step singleton-output emitter, respectively. |
| `b2b_hostedSource` | Two prescribed seams composing native rewind, the cleaned verifier, and a final native rewind. |
| `b2b_tapeCount`, `b2b_wordTape` | Three word tapes followed by verifier, identity, and setup banks, each doubled for cleanup. The word indices are certificate, buffer, CAP. |
| `b2b_bankEmb`, `b2b_callEmb`, `b2b_singleEmb` | A contiguous offset selection; a selection mapping virtual buffer to tape one and payload to the verifier bank; and a singleton selection. |
| `B2bTestPhase`, `b2b_testState`, `b2b_testPhases`, `b2b_testRedirect`, `b2b_testTM` | The six-phase test and its dependent control: anchor, identity capture, rewind, copy, verifier call, verdict. Both verdict exits remain unredirected within the test. |
| `B2bBodyPhase`, `b2b_bodyState`, `b2b_bodyPhases`, `b2b_bodyRedirect`, `b2b_bodyTM` | A test followed, only on rejection, by buffer clear and successful certificate increment back to the anchor. Acceptance stays at the designated live exit. |
| `B2bHostPhase`, `b2b_hostState`, `b2b_hostPhases`, `b2b_hostRedirect`, `b2b_host` | Five setup phases, one counter-loop phase, the embedded final test, and two answer phases, packaged as one finite machine with an additional counter tape. |
| `b2b_setupCfg` | Certificate and counter words, blank other tapes, origin work heads, selected native position, and empty output. |
| `b2b_trialCfg` | Certificate, buffer, and capture words; blank banks; configurable buffer/CAP heads; all other work heads at zero; empty output. |

The six private instances supply finite enumeration and decidable equality for the three dependent control families. They add no execution mechanism.

Standards used: the exact-head [audit template](https://github.com/Shilun-Allan-Li/tcslib/blob/cef76e00/audits/TEMPLATE.md), [policy](https://github.com/Shilun-Allan-Li/tcslib/blob/cef76e00/policy.md), and [workflow](https://github.com/Shilun-Allan-Li/tcslib/blob/cef76e00/workflow.md). The only packet correction identified beyond the already recorded screen-baseline erratum is finding 1.

**Notation glossary.** `x` is the input and `n` its length; `u` is a certificate; `++` denotes concatenation. `L` is the language and `V` its verifier language. `C,c` specify certificate length `Q`; `M_V,M_I,M_P` are the fixed verifier, identity, and unary-setup machines; `.k` is their work-tape count. `K` is the full host tape count. `c_V,e` bound verifier space; `c_I,c_P` bound identity/setup space. `W` is the common whole-run head radius; `T` is the final halting time, `t` a prefix time, and `j` a tape index. `head_j(t)` and `visited_j(T)` denote that tape's head position and visited-cell set. `D,f` are the fixed polynomial-ledger coefficient and degree; `r` indexes certificates. `enumWord` and all Lean identifiers retain their source meanings.

PASS — 0 blockers / 0 majors / 1 minor / 4 notes.
