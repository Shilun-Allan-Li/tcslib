External audit — Arora–Barak Chapter 1 fill campaign, Epoch 4

**Blocker: none identified. Major: none identified. Minor: three. Notes: six.**

The timed construction satisfies the five binding obligations. In particular, its timeout proof covers divergent sources without assuming that the simulated source eventually halts. I independently reproduced the fresh 34-module elaboration, the eight headline axiom footprints, and the absence of `sorryAx` dependencies throughout the imported campaign declarations. These conclusions concern the frozen statements and supplied implementation; they do not dispose of either human-reserved design question or constitute blanket approval of the repository.

The primary input was `epoch4-bundle.md`, SHA-256 `e0ba4b1480182a81b4f541ad279f461c1c685c5e4d02ea5050456b9424710230`. Its 34 extracted Lean modules are byte-identical to [commit `fd7bb18e5652306f79c8db1fa3d15d8877b17599`](https://github.com/Shilun-Allan-Li/tcslib/commit/fd7bb18e5652306f79c8db1fa3d15d8877b17599). Line references below refer to individual files, not bundle lines. Supplementary evidence came from fetched Git history, a cached Lean/mathlib installation, and a cached delivery archive; these sources are distinguished from the attachment below. No repository changes were submitted.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | Audit pack · attestation 2 | Both the post-refactor and post-fill sweeps were at this zero-admission tree content. | As written, the sentence conflates two different trees. `ff2161e4:Universal.lean` still ends `timed_universal` with `sorry`; the plan correctly records one expected admission warning at that stage. My fresh sweep of `fd7bb18e` has zero such warnings. | Separate the historical checks: post-refactor had one expected admission; post-fill had none. Do not describe both as checks of the same tree content. |
| 2 | minor | `UniversalInterpreter.lean:246–256` · `universalEval_step` | Every promoted declaration has statement-prose documentation. | This newly public lemma's entire docstring is “Read-based administrative step rule.” That is a label, not a natural-language statement of its hypothesis and conclusion, under `policy.md` §2. All 151 promotions have docstrings; mechanical presence checking therefore passes, but the stronger prose-quality claim is false. | State that when the controller selects the specified administrative action at the represented reads, one step advances the table/state cursors and performs the optional state-tape write while preserving the other configuration fields. No formal change is needed. |
| 3 | minor | Audit pack · attestation 1; `Universal.lean:24`; plan §5, design question 1 | Current location/layout descriptions match the integrated tree. | There are **two inter-file moves and one within-file relocation**: `exists_codeTM` remains in `Encoding.lean`. `Universal.lean` no longer “holds only the public statements”: it contains 130 new private declarations. The plan still says the private bridge “stays … in `Encoding.lean`,” although it is now in `MathlibBridge.lean`. | Correct the location accounting and update the present-tense descriptions. Record the implemented quarantine while explicitly retaining the unresolved human design decision. |
| 4 | note | `Universal.lean` · `timedPrefix_*`, `timedCanon_*`, `timedAction`, `timed_clock_success`, `timed_flush` | Clock separation, buffering, one decrement per transition, halt interception, and both deadline boundaries are implemented. | The configuration identities connect the actual finite machine to the source and retain the final transition's emission. See the source trace and specific-question answers below. | No correctness change identified. |
| 5 | note | `Universal.lean:2314–2365, 2808–2829` · `timed_interpret_finishes`, `timed_universal` | Timeout holds even when the source never halts. | The induction is on remaining numeric credit, with arbitrary source configuration. At zero credit, a live source reaches the pending-action checkpoint, then underflows and really halts with `[false]`. No eventual source-halting premise occurs. The separate first-halting-time argument in `timedCapture_start` is used for the canonizer stage only. | No correctness change identified. |
| 6 | note | `Universal.lean` · `timedStartupBound`, `timed_interpret_finishes`, `timed_cost_bound` | The realized coefficient is independent of input and deadline. | The startup, clock, terminal lookup, buffer flush, and induction slack re-sum to the advertised bounds and `C = S + B + 14`. Emitting at every source step stays within the ledger. | No cost repair identified. |
| 7 | note | Merge refactor; eight headline declarations | The refactor preserves audited content and the fill preserves public statements. | Reproduced 21/53/77 promotions, ordered and multiset comparisons, unchanged relocation blocks, and exactly one added declaration-body line, `rfl`. Removing that line in an isolated copy reproduces the residual reflexive goal. All eight headline headers are byte-identical to `b519a004`. | Retain ordered comparisons and namespace/context checks alongside name counts and multisets. |
| 8 | note | Campaign closure · attestations 2–6 | The integrated tree is admission-free and delivery artifacts agree. | Fresh compilation and axiom checks pass; all 3,984 imported campaign constants have no `sorryAx` dependency. The supplemental cached archive's manifest, flat source, patch, and bundle agree. Historical maintainer executions themselves are not independently observable. | Preserve the distinction between reproduced artifact properties and historical execution claims. |
| 9 | note | Plan §5 · both open design questions | Correctness review leaves architectural disposition to humans. | Both questions remain explicitly open; the six size escalations have recorded explanations. The new timing proof does not require accepting or rejecting either architectural choice. | No design ruling is made. |

The frozen timed statement, read from its quantifiers, supplies one finite binary machine for each effective scheme, then a natural-number constant for each code, uniformly over all inputs and deadlines. Success includes first halting on the deadline transition. Timeout requires only failure to halt by that deadline, not failure to halt forever. `ComputesInTime` is equivalent to the halted-state and exact-output predicates at the specified time because halting is absorbing. The implementation proves the stronger unconditional bounded-answer lemma `timed_computes`, then derives both public clauses from it.

The following source trace checks the binding obligations.

1. **Clock/code separation.** `timed_input_layout` proves

   \[
   \texttt{pairEncode (pairEncode bs α) x}
   =\bigl(\texttt{bs.flatMap}\,(b\mapsto[b,b,b,b])
      \mathbin{++}[\mathrm{false},\mathrm{false},\mathrm{true},\mathrm{true}]\bigr)
      \mathbin{++}\texttt{pairEncode α x}.
   \]

   `timedPrefix_complete` ends with parser output exactly `α`, clock tape exactly `bs`, and physical input position `4 * bs.length + 2 * α.length + 7`. `timedCanon_start` explicitly initializes `c.canonizer` on **`α`**; `timedCanon_complete` invokes `c.canonizer_computes α`. Neither the clock-carrying payload nor the suffix is substituted for that input. The preservation identities also retain the clock's contents and head.

2. **Buffering and final emission.** `timedAction` sets its real output to `none` and writes a source emission to lane 5, advancing that head exactly when an emission exists. Its successor is always live: a native halted successor becomes `emitStart`. The full configuration identity

   \[
   (\texttt{timedAction a}).\texttt{apply}\,(\texttt{timedLift cfg bs})
   =\texttt{timedLift (a.apply cfg) bs}
   \]

   holds also when `a.state = none` and `a.output = some b`. Thus the halting transition's bit is in the buffer before the output phase starts. `timedLift` has real output `[]`; `timed_clock_timeout` quantifies over arbitrary accumulated buffered output yet concludes exactly `[false]`. On success, `timed_flush` concludes exactly `true :: cfg.output`. Earlier canonizer emissions are also captured: `timedCaptureCfg.output = []`.

3. **One borrow per source transition.** For every fixed-width clock word, `timedBorrow_length` preserves its width, `timedBorrow_underflow` characterizes numeric zero, and positive credit satisfies

   \[
   \texttt{timedValue (timedBorrow true bs).2}+1
   =\texttt{timedValue bs}.
   \]

   `timed_clock_success` performs this borrow and exactly one pending native action. `timed_clock_timeout` performs no pending source action. Zero credit need not have an empty representation: after successful decrements it can be a nonempty all-zero word, which the underflow theorem covers.

4. **The stopped controller is confined to proofs.** `timedCut_live_block` requires only a live source and a bounded table cursor. It returns a live `applyRecord` checkpoint, plus a separate equality identifying the effect of applying that record. If the stopped controller had reached any earlier `applyRecord`, its next step would halt and absorption would contradict the certified live endpoint. This is the premise used by `timedCut_no_record` and `timed_replay`; replay therefore transports a proved administrative trace. The delivered definition expands through `timedCaptureTM`, `timedCanonTM`, and `timedInterpreter`, whose ordinary actions use `universalInterpreter`. It does **not** invoke `timedCutInterpreter`.

5. **Finite termination, including divergence and inclusive deadlines.** In `timed_interpret_finishes`, the source configuration is arbitrary; the hypotheses are the cursor bound and `timedValue bs = r`. Both the zero and successor cases first inspect whether the source is already halted. A halted source flushes immediately. Otherwise, zero credit takes the stopped lookup and timeout branch; positive credit applies one transition and invokes the induction hypothesis on its actual successor with credit reduced by one. Consequently, a final allowed halting transition reaches the halted branch even with zero remaining credit.

   For a divergent source, every successor remains live. There are exactly `t` successful source transitions, followed by a finite stopped lookup and the underflow branch; there is no application of transition `t + 1`. For a source that halts later than the deadline, the same argument applies to its live deadline prefix. In the final public proof, hypothetical source halting at time `t` would itself supply the forbidden output witness through `computesInTime_iff`; this establishes the live-state condition without assuming anything about later times.

   The apparent eventual-halting premise in `timedCapture_start` does not compromise this argument. Its application in `timed_initialized` is to `timedCanonTM c`; `timedCanon_complete` discharges that premise using the effective scheme's total canonizer contract. It is never an eventual-halting premise about `c.decode α`.

For the cost calculation, use the delivery report's quantities:

\[
\begin{gathered}
M=c.\mathrm{decode}(\alpha),\quad A=|\alpha|,\quad L=|M.\mathrm{serialize}|,
\quad N=M.\mathrm{numStates}+1,\quad q=M.\mathrm{tm}.q_0.\mathrm{val},\\
h=|\mathrm{Nat.bits}(M.\mathrm{numStates})|,\quad
K=c.\mathrm{canonizerTime}(A),\quad w=|\mathrm{Nat.bits}(t)|,\\
S=3A+K+L+2h+2q+16,\qquad B=3L+5N+20.
\end{gathered}
\]

| Phase | Cost | Source certificate |
|---|---:|---|
| Clock/code parsing | `4w + 2A + 6` | `timedPrefix_complete` |
| Virtual canonizer preparation | `A + 2` | `timedCanon_start` |
| Canonization of the code | at most `K` | `timedCanon_complete` |
| Capture-to-interpreter transfer | at most `1` additional | `timedCapture_start` |
| Table rewind and source initialization | `L + 2h + 2q + 7` | `timedCut_Interpreter_initialize`, `timed_replay` |
| Stopped lookup | at most `B` | `timedCut_live_block` |
| Positive borrow and application | `2w + 4` | `timed_clock_success` |
| Zero-credit check and timeout | `2w + 3` | `timed_clock_timeout` |
| Success output for buffer length `ℓ` | `2ℓ + 3` | `timed_flush` |

Startup sums to

\[
(4w+2A+6)+(A+2)+K+1+(L+2h+2q+7)=4w+S.
\]

The stopped lookup omits the audited block's final source-action application; its explicit subphase sum still fits `B`. The application is charged once in the clock phase. Rewinding, borrowing, and dispatching cost

\[
\begin{aligned}
1+(w+1)+w+1+1&=2w+4 &&\text{(successful application)},\\
1+(w+1)+w+1&=2w+3 &&\text{(timeout)},\\
1+(\ell+1)+(\ell+1)&=2\ell+3 &&\text{(success output)}.
\end{aligned}
\]

The induction's bound is `(B + 2w + 8)(r + 1) + 2ℓ`. At zero credit, the live case costs at most `B + 2w + 3`; the halted case costs `2ℓ + 3`. Both fit. With positive credit, `MultiTapeTM.step_output` gives successor output length at most `ℓ + 1`, including an emission on the halting transition. Therefore

\[
\begin{aligned}
\text{total remaining cost}
&\le (B+2w+4)+(B+2w+8)r+2(\ell+1)\\
&\le (B+2w+8)(r+1)+2\ell.
\end{aligned}
\]

Width is unchanged during this induction. Initially `r = t` and `ℓ = 0`. `timed_bits_length` proves `w ≤ t`, also at zero. The final absorption into the quadratic bound follows term by term:

\[
\begin{aligned}
4w+S&\le(S+4)(t+1)^2,\\
B+2w+8&\le(B+10)(t+1),\\
4w+S+(B+2w+8)(t+1)
&\le(S+B+14)(t+1)^2.
\end{aligned}
\]

Thus `C = S + B + 14` depends only on the fixed scheme and code. Neither `x`, `t`, nor the clock width enters it. These estimates include the extra unsuccessful lookup at exhaustion; they do not charge merely the number of simulated source transitions.

The six specific questions have the following dispositions.

| Question | Answer and evidence |
|---|---|
| 1. Deadline zero; source first halts at time one | **Timeout.** Initialization is live, so no output satisfies `ComputesInTime … 0`. The empty clock still has both delimiters. Startup completes, stopped lookup prepares a record, and underflow halts with `[false]` without executing it. The success antecedent is false for every output. |
| 2. Final transition both halts and emits | **The bit is retained.** `timedAction_apply` appends it to the buffer while changing the physical successor to live `emitStart`. The induction then takes the halted branch before requiring further credit. `timed_flush` emits the success tag and the complete source output. |
| 3. Empty code, concrete scheme | **Covered.** The input is the quadrupled clock followed by `[false,false,true,true,false,true]` and verbatim `x`; the canonizer receives `[]`. For the concrete fallback, `L = 84`, `N = 1`, `q = h = A = 0`. Hence `S = K + 100`, `B = 252 + 5 + 20 = 277`, and `C = K + 391`, where `K = c.canonizerTime 0` is finite and independent of the deadline/input. The fallback itself halts silently after one source transition. |
| 4. Empty input with positive deadline | **Covered without a nonemptiness assumption.** `timed_initialized` instantiates the inherited boundary embedding with prefix `pairEncode (Nat.bits t) α`. The physical head is at prefix length plus one, the right blank; the marker head is at virtual position one, adjacent to the marked virtual left boundary at zero. `universalInput_read` and `universalInput_move` quantify over arbitrary `x`, including `[]`. |
| 5. Emission on every step | **Within budget.** Each source step increases buffer length by at most one, so a source first halting on step `t` has `ℓ ≤ t`, including its last emission. The induction explicitly pays two units per possible added bit and includes the terminal `2ℓ + 3` flush. |
| 6. Stopped-controller leakage | **None found.** The machine definitions use the live interpreter described above. `timed_replay` requires a proved live endpoint; absorption excludes an earlier stopped action. The selected source action is applied only by the successful clock branch. |

The split checks used the actual endpoints of the linked [refactor comparison](https://github.com/Shilun-Allan-Li/tcslib/compare/2832663b...ff2161e4) and [fill comparison](https://github.com/Shilun-Allan-Li/tcslib/compare/e726238f...fd7bb18e), fetched through Git. I removed nested comments, normalized the declared visibility changes and replicated module wrappers, and compared both ordered code and line multisets. I separately checked namespace/open/section contexts and the relocated declaration blocks. A multiset or a public-name count alone was not treated as a freeze proof.

| Split | Explicit declarations before/after | Promotions | Ordered comparison |
|---|---:|---:|---|
| Encoding → Encoding/CodeParser/MathlibBridge | 168 / 168 | 21 | Identical after isolating the unchanged `exists_codeTM` relocation |
| Universal → four modules | 107 / 107 | 53 | Identical |
| Oblivious → five modules | 240 / 240 | 77 | Identical declaration order; sole body addition is the recorded `rfl` |

Each promotion has a syntactic cross-module use in comment-stripped code. The two inter-file moves (`exists_effectiveMachineCode`, `Turing.FinTM.Oblivious`) and the within-file relocation (`exists_codeTM`) preserve their declaration/docstring blocks byte-for-byte over the refactor span. The added `rfl` is in `dataCfg_backward_step`; deleting it from an isolated copy produces exactly one unsolved, reflexive configuration-equality goal, while the original module compiles. This supports the reported definitional-equality repair; I did not reconstruct the rejected alternative Universal cut point.

The public declaration counts are 227 and 378, with no old name lost and the 151 gains exactly matching the promotions. The fill adds 130 private declarations and no public declaration, changes no other Lean module, and removes exactly the final `sorry` line. The three universal theorem headers and docstrings are byte-identical across the fill. All eight headline theorem headers are byte-identical to the epoch-3 audited commit. Apart from the permitted relocation and visibility changes, the ordered source comparisons also preserve the previously audited bodies.

The eight headline checks cover `Turing.universal`, `Turing.universal_quadratic`, `Turing.timed_universal`, `Turing.exists_effectiveMachineCode`, `Complexity.oblivious_of_mem_DTIME`, `Complexity.UC_not_computable`, `Complexity.UC_computable_of_HALT_computable`, and `Complexity.HALT_not_computable`.

Import redistribution is consistent with the new dependency chains and the fresh successful sweep. The new direct `Nat.Bits` import in `ObliviousSchedule` introduces no globally new Mathlib dependency. The fill's sole added import is `Mathlib.Tactic.FinCases`. `TMToPartrec` is directly imported only by `MathlibBridge`; the universal evaluator's own module chain does not require that existence-proof module. The facade and sweep order include all nine new modules.

Attestations 1–7 are assessed individually below.

| Attestation | Independently reproduced | Limits or correction |
|---|---|---|
| 1. Freeze/drift | Attachment plus fetched history: 227 → 378 public declarations; exact promotion set; ordered/multiset split comparisons; unchanged relocation blocks; sole added `rfl`; 130 private fill declarations; all eight frozen headline headers. | Correct “three changed files” to two inter-file moves plus one within-file relocation. Earlier closed mathematics was not re-audited. |
| 2. Elaboration | One new full sweep, on a separate checkout at `fd7bb18e`, using an initially empty campaign olean directory: **34/34**, exit **0**, errors **0**, gate failures **0**, admission warnings **0**, fresh oleans **34**. Lean **4.25.0**; mathlib **`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`**. The checker preserves process failure and requires fresh output. | Standard cached dependency oleans were reused; Lean/mathlib themselves were not rebuilt or reverified. I cannot observe the maintainer's historical executions. The post-refactor zero-admission wording is incorrect. Ordinary linter warnings remain. |
| 3. Axioms | Fresh `#print axioms` for all eight named theorems gives exactly **`[propext, Classical.choice, Quot.sound]`**. A separate dependency traversal of **3,984 imported campaign constants**, including private/generated declarations, finds **zero** depending on `sorryAx`. | This is a new check of the integrated sources, not authentication of a historical maintainer log. |
| 4. Soundness scan | All 34 source modules contain no literal `sorry`/`sorryAx` tokens. Comment-aware scans find no added axiom or listed bypass. The fill adds no options, has the single advertised import, and contains one ordinary `decide` expression, not `native_decide`. | Imported standard Lean/mathlib trust remains; the scan is scoped to the campaign, as requested. |
| 5. Policy | The repository linter reports **zero campaign FAILs and six WARNs**, with exactly the named files/sizes and recorded justifications. Its 14 other FAILs are confined to out-of-scope `NPReductions`. | Presence checks do not establish prose quality; finding 2 supplies a counterexample. Current-location prose also needs finding 3's corrections. |
| 6. Delivery provenance | The supplementary cached `epoch4-A.zip` has the seven standard entries. All six manifest digests verify. Its flat source equals the integrated source; applying its patch to `ff2161e4` reproduces the bundle commit's tree. The bundle requires precisely `ff2161e491faf61ce42c60a23f02a80c62e33c83`. Its report equals the attached report; its log lists all 34 modules in order, with no errors/admission warnings, and its four axiom lines agree with my checks. | The archive and raw logs were **not in the uploaded Markdown bundle**; this check used an available cached delivery. It does not establish which bytes the maintainer historically received or how many times they ran checks. Agent commit `6ed6cdd8` and integrated commit `37d70522` contain the same `Universal.lean` blob. |
| 7. Human-reserved items | Both questions remain explicitly open; the plan records the mechanical quarantine, interpreter split, and six size escalations. | Update the stale bridge-location sentence without closing the question. No architectural verdict is issued here. |

For identification, the supplemental archive SHA-256 is `91a95a29dc27383e23e00d4bd17f4bbaf2b89c09df4adf37ebf2ac3357055bf4`; its flat `Universal.lean` SHA-256 is `d6e9332ccba8a0889804e7bf30d372c6c8c6903922b1e34040af87fe302e71a4`. The patch/bundle tree comparison yields `b166d55bc45a767d90f86468bf02e34843c2b098`. None of these supplementary artifacts was accepted as a substitute for the new source, elaboration, and dependency checks.

Notation glossary: `c` is the fixed effective scheme; `α` is the code; `x` is the input; `t` is the deadline; `bs` is a fixed-width clock word; `b` is a Boolean bit; `M`, `A`, `L`, `N`, `q`, `h`, `K`, `w`, `S`, and `B` are defined in the cost display above; `C = S + B + 14`; `r` is remaining source-transition credit; `ℓ` is the current buffered source-output length; `|·|` denotes list length; `++` is list concatenation; `cfg`, `src`, and `a` denote the configurations and action in the cited Lean declarations. Other backticked identifiers are names already present in the audited sources.
