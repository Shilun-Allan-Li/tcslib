**Gate: CLOSE — 0 blockers, 0 majors, 2 minors, 7 notes.** No proof defect requiring a change was found in the seven contracts or their 271 new private declarations. The bridge restoration and ledger, forwarding-loop summation, and P2 dispatch/seam arguments meet the standing construction obligations. Two documentation findings require errata; neither defeats the proof gate.

Audited `emitter-fill-bundle.md`, SHA-256 `5ac26ba61431eef5fe5777117381ae62d8b0b145ccd13a30868491e5b7b2b4b0`. Its 22 attachment headers match the manifest. Intended destination: `audits/emitter-fill-findings.md`. References use extracted-file line numbers; `Build/` abbreviates `TCSlib/Complexity/TuringMachine/Build/`.

This is a source-level proof audit with independent calculations, source comparisons, and bounded transition-table checks. No Lean/Lake/Elan executable was on the audit PATH, and the attachments are not a complete buildable checkout. Compiler and kernel-traversal results below are **supplied evidence**, not executions reproduced by this auditor. The five attestation verdicts and their limits appear in finding 9. The frozen statements, campaign admissions, A2 reverse host, and correctness of the harvest originals were not reopened. No GitHub interaction or modification of the supplied pack, sources, or earlier findings occurred.

1. **MINOR — The final axiom log's success sentence contradicts its declaration-level results.**

   **Location:** `audits/logs/emitterP2-axioms.log:4–11,28`.

   All seven emitter contracts have printed `ROOTS ...: []`. Nevertheless, line 28 says that “the six remaining spec contracts” are “at their own roots.” That is the earlier partial-integration expectation, not the displayed final result. Its `EMITTER 7/7` prefix also contradicts that clause.

   **Resolution:** record an erratum identifying the stale sentence; correct the checker/status message for future runs to say all seven emitter roots are empty, with only the named campaign frontiers retaining roots. Preserve the sent pack and historical log. The individual root lines support closure; this finding does not allege a remaining emitter admission.

2. **MINOR — Three details of the span attestation overstate or misdescribe the attached record.**

   **Location:** `audits/evidence/emitter-fill/span-attestation.md:3–5,40–42,78–83`; pack attestations 1–2; the W/L/P/P2 REPORTs and final lint log.

   | Claim | Attached evidence and correction |
   |---|---|
   | `d7b5b6f9` was the base “every brief pinned.” | W, P, and L report that base. P2 explicitly reports `08884731b3c86d13218470f23dc850c3c96c6314`, with its brief read at `09e10c89` (`batchP2.md:12–15`). Distinguish the **whole-span starting commit** from the **P2 continuation base**. |
   | L's identical `FinCases` import “merges to the same line” as P's. | It occurs in two different owned files: `Build/Loop.lean:7` and `Build/Primitives.lean:9`. Both reports disclose the addition. The accurate description is **one newly imported module, at two import sites**, not one merged line. |
   | Wrappers at 739 lines is “under target.” | The attached lint log explicitly reports `739 lines > target 600`; it is below the 1,000-line ceiling. Convention is under target; Wrappers is under the ceiling. The reported 0 FAIL / 2 WARN remains correct. |

   **Resolution:** record these corrections in the subsequent resolution/evidence record. There is no evidence here of a wrong-base P2 implementation, an undisclosed dependency, or an extra lint failure. Delivery-commit hashes differing from integration-commit hashes are not themselves discrepancies: the attestation explicitly describes patch integration.

3. **NOTE — Both clean-call proofs restore the entire seam and satisfy the audited coefficient.**

   **Locations:** `Build/Loop.lean`, `emCallTrackTM`/`emCall_track_run` (3096–3360), extent/support and clearing (3213–3261,3377–3467), relocation/layout (3685–3756,4044–4223), controller/assembly (4101–4121,4226–4606), public bridges (5645–5711).

   The restoration argument has the necessary hypotheses and uses them:

   - Initially each source data tape is blank; visited and origin markers are installed at zero. Corresponding data/marker/origin heads move together.
   - A source-action microstep performs its write, move, input move, and output **before** storing the successor in the intermediate control. The following stamp marks the new work-head position, even when the stored successor is `none`. Thus a terminal write or move is covered.
   - `emCall_track_extent` includes the origin, current head, and elapsed-time bounds. `emCall_track_support` proves blankness at **every integer cell outside** that interval, by separating the previously scanned write cell from all other cells. This is stronger than a head-position bound alone.

   For one tape at source deadline $T$, put $\ell=hi-lo+1$. The proved facts give

   \[
   -T\le lo\le0\le hi\le T,\qquad
   lo\le h\le hi,\qquad
   1\le\ell\le2T+1,
   \]

   and the data is blank outside $[lo,hi]$. With $j=h-lo$, the cleaner first reaches the left end, erases the entire marked interval, and then uses the retained origin marker to return to zero. Its phase counts are

   \[
   (j+2)+(\ell+1)+(hi+1)
   \le3\ell+4\le6T+7.
   \]

   `emCall_cleared_all` uses outside-support blankness to turn this interval erasure into equality with the **entire blank tape**. The origin marker is erased only at the final origin step. Blank holes in source data cannot stop these marker-guided scans.

   Relocation preserves inactive tapes and their heads: an unselected slot receives `(none, 0)` and retains its ambient frame. The triple/pair inverse and disjointness lemmas cover every host index. `emCall_banks_run` composes complete frames, so cleaning a later bank cannot dirty an earlier bank, argument, or capture.

   Write $k=M.k$, $a=|arg|$, $b=|cap|$. The actual assembly proves:

   | Phase | Charged time |
   |---|---:|
   | Tracked evaluation, virtual-right-boundary normalization, first bank dispatch | $2T+a+4$ |
   | All $k$ cleaners, including each next-bank dispatch | $k(6T+8)$ |
   | Finalizer dispatch and complete argument/capture handling | $a+3b+6$ |

   The finalizer itself takes exactly $1+(a+1)+3(b+1)=a+3b+5$. Its extra entry dispatch explains the final `+6`. Hence

   \[
   \begin{aligned}
   t&\le(2+6k)T+2a+3b+8k+10,\\
   &(24+13k)(T+a+b+1)
      -\bigl((2+6k)T+2a+3b+8k+10\bigr)\\
   &\quad=(22+7k)T+(22+13k)a+(21+13k)b+14+5k\ge0.
   \end{aligned}
   \]

   Thus the coefficient is exactly the requested shape $6+13k+3K=24+13k$ with $K=6$. No comparison with a time bound occurs in `emCallTM`: evaluation and cleaning dispatch on observed return states. Padding a source deadline after its actual halt is used only in the proof; absorption preserves the tracked endpoint and interval.

   `emCall_finish_final` establishes all five configuration fields. Install mode retains only `cap` on tape zero and emits nothing; emit mode retains `arg`, emits exactly `cap`, and clears capture. Both restore all heads and native input position 1. The native input is not scanned: the normalization scan is over the virtual argument.

   The layout has $3k+2>0$ tapes, including when $k=0$; the empty bank induction then costs zero. Empty argument and result follow the same blank-boundary transitions. Finally, the exit is silent and absorbing on arbitrary configurations. Cutting at its least visit preserves the full endpoint, and its control summand differs from entry, proving positive time and the exported strict-interior exclusion.

4. **NOTE — The forwarding host has its own valid summation proof and executes exactly rounds $0,\ldots,R$.**

   **Locations:** `Build/Loop.lean:4611–4656,4896–4932,5185–5455,5508–5596`; inherited `Turing.loop_run:140–180` and debit lemmas.

   `emLoopHost` replaces only the body-dispatch branch with padded `emitAction`. Fuel is still captured; the old payload tape stays blank and stationary. Thirteen corresponding fuel/countdown helper declarations agree with their inherited counterparts after host-name normalization and removal of comments/whitespace. The changed body simulation is separately proved.

   If $P_p(c)$ prefixes a configuration's output by $p$, its state and scanned symbols are unchanged. In a live step, output associativity gives

   \[
   (p\mathbin{++}c.output)\mathbin{++}a.output.toList
     =p\mathbin{++}(c.output\mathbin{++}a.output.toList).
   \]

   Halted steps are identities. Componentwise equality followed by induction yields `emLoop_step_prefix` and `emLoop_run_prefix`:

   \[
   \operatorname{runFrom}(P_p(c),t)
     =P_p(\operatorname{runFrom}(c,t)).
   \]

   `emLoop_sum` uses the correct shifted induction. For $N=1$, the only segment halts with `p ++ chunk 0`. For $N>1$, the first segment reaches configuration 1 with prefix `p ++ chunk 0`; applying the induction hypothesis to `cfg (i+1)` and `chunk (i+1)` gives

   \[
   t\le B+(N-1)B=NB,
   \qquad output=p\mathbin{++}\operatorname{flatMap}(chunk,[0,\ldots,N-1]).
   \]

   The clean-output hypothesis is retained for each shifted starting configuration. This does not substitute an emitting endpoint into the Boolean/empty-output `loop_run`. In the comment-stripped **entire Loop source**, `loop_run` occurs only at its declaration, and `emit_run` has no occurrence. Forwarding uses `emLoop_forward_apply`/`emLoop_forward_run`; no concurrent W proof is cited. Byte-for-byte preservation of the earlier `loop_run` is separately limited by the unavailable baseline evidence, as stated in finding 9.

   The release bit allows the initial anchor step; the live endpoint and strict-interior exclusion justify the later anchor stop. The body's last action is forwarded before that silent stop, so its last emission is retained. Prefix commutation carries the chunk through debit and underflow; find-mode underflow appends no verdict bit.

   Startup enters round zero before any debit. The existing debit value/length lemmas give success after round $i$ exactly when $i<R$. Thus $N=R+1$, including one round when $R=0$. Writing $T$ for the common budget at the fixed input and using fuel width at most $T$,

   \[
   \begin{aligned}
   t_{startup}&\le(5T+7)+(T+2)=6T+9\le10(T+1),\\
   t_{round}&\le T+2T+5=3T+5\le10(T+1),\\
   t_{total}&\le10(T+1)+(R+1)10(T+1)=10(T+1)(R+2).
   \end{aligned}
   \]

   No additional emission-length premise is inserted or needed.

5. **NOTE — P2 correctly assembles the clean modules, including equal entry/exit and the exact rejecting seam.**

   **Locations:** `Build/Primitives.lean:6041–6512,6516–6735,6776–7409`, especially `emitterP2_call_segment`, `emitterP2_words_clean`, `emitterP2_body_round`, and `emitterP2_closed`.

   The two `exists_installCallTM` witnesses are extracted once, outside the input/round quantifiers. Their positive tape counts support a fixed candidate / width-module / length-module layout. Selection/inverse/frame equations preserve whole inactive banks, not just their distinguished words. Preparation copies the literal candidate and the actual native suffix, restores the native input and all preparation heads, and detects past-end by a nonblank candidate cell facing the native right boundary.

   The module calls do not test exit at time zero. `widthStart`/`lengthStart` unconditionally execute the entry action. In `emitterP2_call_segment`, the remaining local time $j$ corresponds to source time $j+1$; every return guard invoked satisfies

   \[
   0<j+1<t.
   \]

   This exactly matches the public bridge guard even if `entry = exit`. The time-zero host state and every embedded module state are separate from the outer anchor. No deadline, `TE`, or width function appears in the native controller table.

   The bridge restores module scratch. The two subsequent erasers remove each complete installed word, including empty words, and restore its head. The verdict survives in finite control. Then

   \[
   \texttt{emitterP2Words k l s [] []}
     =\texttt{stateWord (k+l+1) s}
   \]

   identifies the **entire** remaining layout. Rejection enters `splitRestoreTM 0` at its proved entry, preserves arbitrary candidate bits, appends one true bit only within range, and makes the explicit final anchor transition. Acceptance enters `splitEmitTM 0` with its full required input/head configuration and emits bits from the native input. Past-end preparation bypasses both evaluators, erases its words, and returns to the unchanged candidate. Every round has the initial departure step, so this branch is positive independently of any cleaner's zero-tape behavior.

   The envelope is assembled before assuming acceptance. Let $n=|w|$, $m=|s|\le n+1$, $u=\mathrm{Nat.bits}(f(m))$, $v=\mathrm{Nat.bits}(|w.drop\ m|)$, and

   \[
   H=TE(n+1)+n+2\ge2.
   \]

   With the length evaluator's constant $d$ and the call constants $c_C,c_D$, the supplied proofs establish

   \[
   \begin{aligned}
   |u|&\le TE(m)\le TE(n+1),& |v|&\le d(|w.drop\ m|+1)\le dH,\\
   t_C&\le2c_CH,&t_D&\le c_D(2d+1)H,\\
   m+n+|u|+|v|+10&\le(d+8)H.
   \end{aligned}
   \]

   Consequently the native round bound is at most

   \[
   \bigl(2c_C+c_D(2d+1)+10(d+8)\bigr)H.
   \]

   `emitterSplit_of_body` absorbs fuel generation and the $n+1$ searched candidates into the frozen exported envelope. Startup is the genuine empty-word anchor at time zero. The final public proof is literally the single application `exact emitterP2_closed f E TE hTE hE`. The REPORT's bridge-embedding route is accurate: it uses the proved public bridge instead of assembling the predecessor's bank machinery again.

6. **NOTE — P's conditional reduction, candidate charging, and simultaneous cleaner have the claimed contracts.**

   **Locations:** `Build/Primitives.lean:4443–4550,4698–4820,5484–5690,5908–5953`.

   `emitterSplit_of_body` requires positive rounds, strict-interior anchor exclusion, and the exact complete rejecting configuration. Its invariant is `s.length ≤ w.length + 1`, preserved by `splitStep`; its fuel value is the native input length. `emitterSplit_find`/`emitterSplit_result` identify the ordered first success on candidates $0,\ldots,n$, rather than using monotonicity of $f$. Exhaustion remains `[]`.

   `emitter_width_budget` first invokes `hE s` at `TE s.length`; the output-growth bound is applied to that very computation. Only then does `hTE` enlarge the deadline to `TE (w.length + 1)`. There is no composition-size surrogate inside `TE` and no accepted-equation assumption in this charging step.

   The comparator reads complete optional-symbol words. Before the longer word ends, at least one scanned cell is nonblank; unequal lengths therefore cannot look equal. Both heads return to zero. The pure identification is

   \[
   \begin{aligned}
   \mathrm{Nat.bits}(f(m))=\mathrm{Nat.bits}(n-m)
   &\iff f(m)=n-m\\
   &\iff m+f(m)=n\qquad(m\le n).
   \end{aligned}
   \]

   `emitter_bits_injective` proves the first equivalence through the binary decoding left inverse; the second is natural-number arithmetic under the displayed range hypothesis.

   `emitterBank_step` projects one native product-controller step to one step of each disjoint triple. `emitterBank_run` iterates that identity. Each cleaner reaches its full blank endpoint by `6*T+7`, and `emitterClear_fixed` keeps that endpoint fixed until the common deadline. Hence all banks are simultaneously blank with heads zero. This is a constant-time-per-product-step construction for each fixed finite tape count; it does not sequentially multiply the deadline by that count.

   At zero source tapes, the entry and all-returned control vectors coincide extensionally, so `emitterBank_first` correctly permits time zero. It claims no positivity. P2 obtains round positivity from its own outer departure and uses the public bridges for cleanup. The predecessor's unused bank helpers remain proved components, not hidden dependencies of a substituted body.

7. **NOTE — W's forwarding proof and both streaming primitives include their boundary and terminal-output cases.**

   **Locations:** `Build/Wrappers.lean:250–300`; `Build/Primitives.lean:7414–7634`; `Build/Convention.lean`, `unaryTokenSplit`.

   `emit_apply` proves four fields by reflexivity and the output field by append associativity. It holds for an action whose successor is `none` and whose output is `some b`: the bit is appended and the host enters `some ret`. `emit_run` then inducts through live source prefixes. The guard excludes only times strictly before the endpoint, so the terminal emission is included. For time zero the equality is reflexive, including an already halted source; positive time from an already halted source cannot satisfy the guard. No injectivity or disjointness assumption is silently introduced.

   `emitterAppendTM` copies $n$ input symbols and emits the fixed bit on the next, halting transition:

   \[
   output=x\mathbin{++}[b],\qquad t=n+1=1\cdot(n+1).
   \]

   If `unaryTokenSplit x = (tok, rest)`, its recursive convention partitions the input, including empty input, a leading false, a terminated token, and an all-true unterminated token. `emitterToken_run` proves

   \[
   output=\mathrm{pairEncode}(tok,rest),\qquad
   t=2|tok|+|rest|+3\le2n+3\le3(n+1).
   \]

   A false delimiter is part of the doubled token; it is not replaced by standalone-marker semantics. The pair separator and final silent blank-reading halt are included in the count. Empty successful splits retain `[false,true]`, distinct from exhausted search's `[]`.

8. **NOTE — Harvest fidelity and the 271-private inventory check out; no foreign private or admission mechanism was found.**

   **Locations:** the new `emCall*`, `emLoop*`, `emitter*`, and `emitterP2*` families; attached `ClassNP/Nondeterminism.lean` `e3c*` templates; design §8; all four REPORT inventories.

   A nested-comment-aware source comparison found:

   | Reimplementation | Compared declarations | Identical after comments, whitespace, and family-prefix normalization |
   |---|---:|---:|
   | `e3c*` → L's `emCall*` | 48 | 47 |
   | `e3c*` → P's `emitter*` | 58 | 57 |
   | L relocation → P2 relocation | 4 | 4 |
   | **Total** | **110** | **108** |

   The two differences were examined: `emCall_clear_first` replaces one `norm_num` with `simp` on the same impossible zero-time equality; `emitter_binary_check` replaces the exponential width expression by arbitrary `f s.length`, retaining the same valid injectivity/subtraction argument. Neither changes the harvested machine semantics.

   The tracking family records visited intervals and origin markers, **not overwritten symbols or a displacement history**. Virtual input clamping uses the same `bufferedSecondCfg_run`/`VirtualTag` interface as the template, including the initial true boundary tag for empty input. The pack's reference to a “recorded actual clamped displacement” must be read subject to the standing R3/§11d correction: no such history log is part of this implementation. There is no new substitution of requested outward motion for the existing clamped virtual motion.

   The exact source-name inventories match their REPORT lists in both directions: W 1, L 119, P 83, P2 68, total 271; every listed addition is private. Current total public/private counts also match the lint log. Comment-stripped `Build/` contains no `sorry`, `admit`, new `axiom`, `unsafe`, `implemented_by`, `extern`, `native_decide`, `_private.` access, or `e3c*` reference. No added notation/macro/initialization mechanism was found. Generic relocation and summation helpers remain local to their owned files, consistent with the deferred deduplication policy; no unreported public export was found.

   Independent finite transition-table transcriptions additionally passed: 29,280 interval cleaners with arbitrary blank holes, 1,922 install/emit finalizers, 1,953 candidate/suffix preparations, 961 complete-word comparisons, 511 token inputs, and 1,022 append cases. These checks include empty words, past-end preparation, unequal word lengths, and both output modes. They corroborate the inspected derivations; they are not exhaustive machine proofs or kernel runs.

9. **NOTE — The five maintainer attestations are corroborated to the following explicit extent; historical and kernel-replay claims remain attested.**

   | Attestation | Verdict and evidence |
   |---|---|
   | **1. Whole-span freeze** | **Inventory/source consistency verified; import wording challenged in finding 2; historical freeze not independently reproduced.** Counts and all four REPORT name lists agree exactly. Current public counts are Convention 8, Wrappers 10, Loop 8, Primitives 18; private totals are 0, 19, 214, 318. The attached Loop and Wrappers SHA-256 values exactly match their REPORTs; P2's 403,447-byte source size matches its REPORT. The pre-fill files and net diff are absent, so zero removals, byte preservation of all old proofs (including `loop_run`), and exactly seven placeholder deletions cannot be established from this final snapshot alone. |
   | **2. Per-delivery verification** | **Not independently reproducible from this bundle; P2-base summary challenged in finding 2.** Checksums, patches, bundles, base objects, reconstruction scripts, and individual replay logs are described but not attached. The reports are mutually consistent about their distinct delivery/integration roles; they are not substitutes for replaying those artifacts. |
   | **3. Elaboration** | **Final log contents verified; execution freshness and intermediate sweeps remain attested.** Exactly 57 `CHECK` entries match the attached module-order list, with zero `error:` lines and a final `FULL_SWEEP_COMPLETE`. Exactly 12 admission-warning lines occur: EXP 1, Nondeterminism 4, SAT 1, Tautology 1, Hardness 5; none is in `Build/`. The source itself contains no Build admissions. The earlier `7→6→4→1→0` integration runs, fresh-olean checks, ordinary-host provenance, and timeout/relaunch history were not independently executed or reconstructed. |
   | **4. Axioms** | **Seven empty-root entries and listed regressions verified as log evidence; footer challenged in finding 1.** The final log prints empty roots for all seven contracts and the named library regressions. It does not print the final axiom sets, helper inventories, or traversal implementation. Thus the standard-triple restriction, opaque/constructor traversal coverage, and 241/387 generated-declaration counts remain claims of the supplied reports/attestation, not independent kernel certifications here. W's REPORT additionally embeds its standard-axiom/module results. No contrary source-level dependency was found. |
   | **5. Policy** | **Current sizes and Build lint result verified; “under target” wording challenged in finding 2.** Extracted line counts are 155, 739, 5,713, and 7,636, exactly as logged. The final lint report has 0 FAIL / 2 WARN. The underlying brief exceptions, D7 decision, and historical “throughout” claim are referenced but not attached; their authority/history remains attested. Repository-wide zero-failure lint is not claimed by P or P2. |

   These qualifications do not identify a proof obstruction. They delimit the gate decision: the supplied proof bodies survive the requested source-level adversarial checks, and the attached final verification records support their reported closure. This report does not certify unprovided Git history or claim an independent fresh compilation. Resolve findings 1–2 through errata while preserving the immutable pack.

**Notation glossary.** Existing Lean identifiers retain their source meanings. `++` is list concatenation, `[]` the empty list, and `|w|` word length. In finding 3, $k=M.k$, $T$ is a source runtime deadline, $a,b$ are argument/result lengths, $lo,hi$ are visited-interval endpoints, $h$ is the current work head, $\ell=hi-lo+1$, $j=h-lo$, $t$ is total elapsed time, and $K=6$ is the stated fixed ledger constant. In finding 4, $P_p(c)$ prefixes configuration $c$'s output by word $p$; $a$ in the action identity is an action; $N,B$ are segment count and uniform segment budget; $R$ is the last round index; $T$ is the common loop budget at the fixed input; $t_{startup},t_{round},t_{total}$ are the indicated durations. In findings 5–6, $w,s$ are native input/candidate words, $n=|w|$, $m=|s|$, $u,v$ are the displayed binary result words, $H=TE(n+1)+n+2$, $d$ is the length-evaluator constant, $C,D$ are the extracted call modules, $c_C,c_D$ their coefficients, and $t_C,t_D$ their call durations; local $j,t$ in the guard are source-step indices/return time. In finding 7, $n=|x|$, $b$ is the appended bit, and `tok, rest` are the token split components.
