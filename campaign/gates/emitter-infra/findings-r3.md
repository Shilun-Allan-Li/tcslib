**Gate: CLOSE — 0 blockers, 0 majors, 1 minor, 4 notes.** The strengthened bridges discharge the cumulative R1-1/R2-1 interface obligation. Section 11c's corrected 4A mapping matches the inherited six-stage contract and its now-attached boundary-check table. The remaining minor concerns construction provenance: the delivered continuation proves interval tracking and clearing, not the overwritten-symbol history/undo algorithm attributed to it. This does not invalidate either bridge or keep the zero-blocker/major gate open.

Intended repository destination: `audits/emitter-infra-r3-findings.md`.
Audited bundle: `emitter-infra-r3-bundle.md`, SHA-256 `7c63ccdc22b2984cb94816f44d658e4689d7b0b5eed75eaa4eca2b9df4bf3dbc`; exactly 36 attachment headers, matching the manifest. The standing round-1/round-2 audit scope and findings are retained. References below use repository paths and extracted-file line numbers.

This is a statements/interface re-audit and a source-level examination of the supplied provenance. The seven emitter contracts remain admitted. The machine-assembly arguments below are mathematical construction arguments, not kernel-checked implementations of those admissions. No Lean, Lake, or Elan executable was available on the audit path, and these attachments are not a complete buildable checkout. No supplied source, pack, or prior finding was modified; no GitHub interaction was performed.

| Cumulative obligation | Round-3 disposition |
|---|---|
| R1-1 / R2-1 — usable prepared-input/clean-return bridge | **Closed.** Both existential witnesses now export positive tape count, and their complete seam equations expose the actual argument/result tape; see finding 2. |
| R1-2 / R2-2 — evidence and 4A customer fit | **Closed.** The original phase-4 boundary table is attached, and the new silent-startup/ordered-emission mapping meets it; see finding 3. |
| R2-3 — P17 supersession marker | **Closed.** The marker is present at the stale paragraph itself; see finding 4. |
| R1-3, R1-4, R1-5 — host routing, token convention, documentation | **Remain closed.** No relevant regression in this repair. |
| R2-4 through R2-8 — bridge feasibility and other positive assessments | **Retained.** Strengthened bridge feasibility is confirmed; the attribution to the continuation needs the minor correction in finding 1. |
| R2-9 — evidence qualifications | The missing REPORT/source and phase-4 table are supplied. Patch/hash and log-content checks succeed; independent compiler execution and some integration-history claims remain qualified in finding 5. |

1. **MINOR — The newly supplied provenance supports track-and-clear cleanup, not the claimed proved history/undo implementation.**

   **Locations:** `TCSlib/Complexity/TuringMachine/Build/Loop.lean:2775–2781`; `machine-library-design.md` §11b item 1 and §11c item 4 (`680–688`); round-3 pack, repair 4. Evidence: `ClassNP/Nondeterminism.lean`, `e3cTrackTM` (`3411`), `e3cTrackCfg`, `e3c_track_run`, `e3cClearTM` (`3177`), `e3c_clear_run` (`3348`), `e3c_track_clearable` (`3877`), `e3c_clear_first` (`3972`), and `e3c_prepared_eval_first` (`4219`); `audits/ch2-epoch3-agent-reports/batchA-cont.md`.

   The bridge docstring specifically attributes recording overwritten symbols and head moves, followed by undo, to the continuation's proved pattern. The pack additionally attributes a recorded actual clamped displacement to this phase family. Inspection of the delivered transition tables does not support those claims:

   | Delivered component | What its table and contract actually establish |
   |---|---|
   | `e3cTrackTM` | Three banks hold current source data, contiguous visited-cell markers, and origin markers. A source-action microstep performs the write/move/emission; a second microstep marks the newly reached cells before any source halt takes effect. |
   | `e3cTrackCfg` / `e3c_track_run` | Exact current source configuration and visited intervals after `1 + 2*t` steps. There is no per-transition tape of old symbols, old states, or input displacements. |
   | `e3cClearTM` | Scan to the marked interval's left boundary, erase data and interval markers rightward, then find and erase the preserved origin marker while returning heads to zero. It clears scratch; it does not reverse source transitions. |
   | `e3cEvalTM` / `e3c_prepared_eval_first` | Captured virtual simulation through actual first halt, with native input head fixed, full output captured, tracked work banks retained, and candidate head normalized to its right boundary. Virtual clamping is implemented by the existing virtual-input machinery, not by a displacement-history log. |

   These are useful and substantively relevant native components. Their distinction from history/undo matters because a proof fill should reuse the contracts that actually exist. The REPORT correctly states that sequencing the complete bank cleanup, clearing administrative/capture buffers, and proving the complete body seam remain open. This audit does not convert that partial checkpoint into a completed bridge or search body.

   **Required documentation correction:** identify the delivered provenance as *visited-interval tracking and clearing*, with the full-bank controller and argument/result handling still to be assembled. If retaining the alternative history/undo sketch, attribute its feasibility to the independent mathematical argument in R2 finding 4; do not call it an already-proved continuation implementation. Preserve the sent pack and record the clarification in the subsequent design/resolution record.

   **Severity rationale:** an inaccurate implementation attribution, not a false contract or unresolved customer interface. The actual track/clear route also fits the bridge envelope, as shown next.

2. **NOTE — The positive-tape repair closes R1-1/R2-1; both bridges now export the required data interface.**

   **Locations:** `Build/Loop.lean:121–122,2790–2803,2823–2837`; `Build/Convention.lean`, `Cfg.ofWords`; `Simulation.lean:494–507`, `bufferTape` and `bufferTape_nat`.

   **Direct interface derivation.** Extract the witness and its new conjunct `hk : 0 < C.k`, and set `i₀ := ⟨0, hk⟩ : Fin C.k`. For every word `w`, the definitions give

   \[
   \begin{aligned}
   (\mathrm{stateWord}\ C.k\ w)(i_0)&=w,\\
   (\mathrm{Cfg.ofWords}\ q\ (\mathrm{stateWord}\ C.k\ w)).\mathrm{workTapes}(i_0)
     &=\mathrm{bufferTape}(w),\\
   \mathrm{bufferTape}(w)(j)&=w[j]?\qquad(j\in\mathbb N).
   \end{aligned}
   \]

   Apply the projection `fun d => d.workTapes i₀` to each bridge's asserted run equality. Consequently its returned tape is **exactly** `bufferTape (f arg)` in install mode and **exactly** `bufferTape arg` in emit mode. The other configuration projections give:

   | Returned component | Install mode | Emit mode |
   |---|---|---|
   | Control | `some exit` | `some exit` |
   | Native input head | `1` | `1` |
   | Tape `i₀` | `bufferTape (f arg)` | `bufferTape arg` |
   | Every tape with nonzero index | Entirely blank | Entirely blank |
   | Every work head | `0` | `0` |
   | Physical output from the clean entry | `[]` | `f arg` |

   This includes the empty-word case: `bufferTape []` is blank at every integer cell, not merely at its head. The old zero-tape witness is excluded by `hk`. For the old append counterexample, cell `|arg|` must now contain `some true` in the installed result, while the unchanged argument contains `none` there. Padding an inactive tape cannot satisfy this equality.

   The existing positive-time and strict-interior exit clauses are unchanged. A live endpoint rules out an earlier physical halt by absorption. Distinct entry/exit states are unnecessary as a hypothesis: a host can allow one source step before testing for return, as in the previously audited release discipline. Tape-block embeddings preserve unrelated host storage. The standing output-prefix commutation result extends the two equations to an arbitrary preexisting output prefix: install preserves it and emit appends `f arg`. Thus the repairs supply the previously missing seam interface, including after earlier emission rounds.

   **Existence and envelope, checked against the actual delivered route.** Let `τ` be the first source halt on `arg`. Total timed computation, live initialization, and absorption yield

   \[
   1\le\tau\le T(|arg|),\qquad
   \mathrm{output\ at}\ \tau=f(arg),\qquad |f(arg)|\le\tau.
   \]

   The tracked/captured prepared-evaluator phase has a genuine argument tape and capture tape even when `M.k=0`. It preserves the argument's contents and reaches a known right boundary within

   \[
   1+2\tau+|arg|+2.
   \]

   For one source tape let its visited interval be `[lo,hi]` and its width be `w`. The supplied extent/support invariants imply

   \[
   -\tau\le lo\le0\le hi\le\tau,
   \qquad w=hi-lo+1\le2\tau+1,
   \]

   with the current head inside the interval and all data outside it blank. The cleaner gives

   \[
   t_{\rm clear}\le3w+4\le3(2\tau+1)+4=6\tau+7.
   \]

   Its exact endpoint restores the data/interval/origin triple to blank with all three heads zero. The initial state differs from its absorbing return state; taking the least return gives a positive first return and the same complete endpoint. Blank holes in source data do not affect the marker-guided scan. The source-action microstep applies even a halting transition's write, erasure, move, and output before the final marker stamp.

   There are only `M.k` triples, a constant of the fixed source machine. Relocate and sequence their cleaners while preserving the argument and captured result. In install mode, erase the old argument from its known right boundary, copy the captured result to tape zero, and erase/rewind the capture. In emit mode, retain and rewind the argument, replay the capture, then erase it. Contiguous words can be erased by scanning left from their right blank and returning one cell right from the left blank; this also handles empty words. These passes and the fixed dispatches cost at most `K(|arg|+|f arg|+1)` for a fixed construction constant `K`. Hence, taking `c = 6 + 13*M.k + 3*K`,

   \[
   \begin{aligned}
   t_{\rm call}
   &\le1+2\tau+|arg|+2
      +M.k(6\tau+7)+K(|arg|+|f(arg)|+1)\\
   &\le c\bigl(T(|arg|)+|arg|+|f(arg)|+1\bigr).
   \end{aligned}
   \]

   Fresh phase controls provide the advertised first-positive-exit discipline. The native input need not be scanned. Neither monotonicity nor computability of `T` is required: dispatch follows observed completion; `τ` and `T` occur only in the analysis. Assembly and its Lean proofs remain fill work, but no additional assumption is needed for the strengthened existence statements. R2's independently derived history/undo alternative remains valid as well.

3. **NOTE — Section 11c closes R1-2/R2-2: its 4A preparation and ordered chunks match the inherited contract.**

   **Locations:** `machine-library-design.md:637–676`; `CookLevin/Hardness.lean:88–206`; `CookLevin/Snapshot.lean:121–134`; `audits/ch2-phase4-reaudit-findings.md:32–47`; `Formulas/CNFEncoding.lean:88–100`.

   The old parser/fallback paragraph is expressly superseded in full. The following checks use the actual inherited table, not merely the resolution record's description of it:

   | Stage | Round-3 mapping and boundary verification |
   |---|---|
   | s1: exact arithmetic | Startup retains the source instance and computes exact `Q(n)`, `m=n+Q(n)`, and `T`. The inherited `C₀=0` and `c₀=0` cases remain included; no time majorization changes certificate length. Complete arithmetic answers, including a halting-transition bit, are captured before installation. |
   | s2: reference simulation | The reference is `false^m`, initialized with source control, blank source work, work heads zero, and virtual input head `1` clamped to `0..m+1`. These are precisely the runs defining `inputPosAt`/`workPosAt`. Empty reference input starts at its right boundary. |
   | s3: output/halt | The source's final tape/head effects occur before its halt becomes internal. Its output is suppressed and its halted configuration remains available for the rest of the horizon. Both early rejection and halting on the final simulated transition are covered. |
   | s4: trajectory | Startup records all source times `0,…,T`: time zero before any source transition, time `T` after the last. Recording and counter operations do not advance the logical source clock. After a halt at time `h`, the position records at all times `h,…,T` are equal to the post-transition positions. |
   | s5: previous visits | For each target time and tape, use the greatest matching time in `List.range t`, exactly as `prevVisit` specifies. At time zero the result is `none`. At times strictly after an earlier halt the immediately preceding time is the greatest match. Sequential retrieval/comparison costs are explicitly retained. |
   | s6: serialization | The prepared records and cursor form the clean persistent word. The cursor traverses the original family order; each member emits its clause fragment, with the unique formula terminator added only to the last chunk. Silent startup and prefix-preserving emission establish the inherited physical-output invariant. |

   Here s2–s4 describe one coordinated simulation/recording controller, as the inherited table specifies. The install call must be used on a producer whose result is the packed preparation records: the bridge preserves that result and clears its scratch. Capturing only the bare verifier's verdict would not produce those records. Section 11c explicitly requires the packed records, so it does not license that substitution or claim the catalog computes them automatically.

   **Round count and exact word.** The six ordered families have the following numbers of members:

   | Family | Members |
   |---|---:|
   | Pin input bits | `n` |
   | Initial block | `1` |
   | State succession | `T` |
   | Input-read wiring | `T+1` |
   | Work-read wiring | `k(T+1)` |
   | Acceptance | `T` |

   Therefore

   \[
   \begin{aligned}
   n+1+T+(T+1)+k(T+1)+T
     &=n+(k+3)T+k+2\\
     &=R+1,
   \qquad R=n+(k+3)T+k+1.
   \end{aligned}
   \]

   This matches `List.range (R+1)` in `exists_emitLoopTM`. Strictly, §11c's phrase “the round count is their sum” refers to **`R+1`**, while its displayed `R` is the last round index/initial fuel value. Its displayed formula is correct; the brief should preserve that distinction. Even `n=k=T=0` leaves two members, so the last-chunk rule has no missing zero-member case; the actual normalized horizon is positive.

   Let `Gᵢ` be the clause list for member `i`, in that fixed order, so \(\varphi_x=G_0\mathbin{++}\cdots\mathbin{++}G_R\). Specify its chunk by

   \[
   w_i=
   G_i.\mathrm{flatMap}(C\mapsto\mathrm{true}::\mathrm{serializeClause}(C))
   \mathbin{++}
   \begin{cases}
   [\mathrm{false}],&i=R,\\
   {[]},&i<R.
   \end{cases}
   \]

   The serializer definition and associativity give

   \[
   w_0\mathbin{++}\cdots\mathbin{++}w_R
   =\varphi_x.\mathrm{flatMap}(C\mapsto\mathrm{true}::\mathrm{serializeClause}(C))
       \mathbin{++}[\mathrm{false}]
   =\mathrm{serialize}(\varphi_x).
   \]

   In particular, an empty template contributes no clause marker; an empty **clause** still contributes its marker and clause terminator. An empty last template still emits the single formula terminator. Calling the complete formula serializer independently on every group would introduce extra terminators and is not this chunk rule.

   The loop invariant can consist of the correctly packed immutable records and a cursor in `0,…,R+1`. Start at zero, advance by `i ↦ min(i+1,R+1)`, and give cursor `R+1` a positive silent self-return. This explicitly supplies the step-closed invariant required even beyond the finitely executed prefix. The loop executes cursors `0,…,R` only; empty group rounds still have positive duration. Clean emit calls preserve the packed argument, and clean install calls update its cursor; phase controls keep the outer anchor out of strict round interiors.

   **Length and time checks.** Expand the serializer directly:

   \[
   \begin{aligned}
   |\mathrm{serializeLit}(v,b)|&=v+3,\\
   |\mathrm{serializeClause}(C)|&=1+\sum_{(v,b)\in C}(v+3),\\
   |\mathrm{serialize}(\varphi_x)|
     &=1+2\,\#\mathrm{clauses}
       +\sum_{(v,b)\text{ occurrence}}(v+3).
   \end{aligned}
   \]

   The pinning contribution is exactly

   \[
   \sum_{j=0}^{n-1}(j+5)=\frac{n(n-1)}2+5n.
   \]

   The inherited normalization gives `T ≥ (m+1)²`, hence `n≤m≤T`. With fixed code width `B` and `N=m+(T+1)B`, every index is below `N=O_M(T)`. Fixed templates give `O_M(n+T+1)` clauses and literal occurrences. Thus

   \[
   |\mathrm{serialize}(\varphi_x)|
   \le1+2\,\#\mathrm{clauses}+(N+2)\,\#\mathrm{literals}
   =O_M(T^2).
   \]

   Preparation is also polynomial without random access. The trajectory and last-visit records occupy `O_M((T+1)log(T+2))` bits under sequential self-delimiting storage. The earlier-record search uses

   \[
   k\sum_{t=0}^{T}t=\frac{kT(T+1)}2
   \]

   position comparisons; charging full polynomial-length scans and rewinds for each still yields polynomial time. Exact arithmetic, packing, native-input copying, complete clean calls, cursor updates, and unary output all receive polynomial budgets. The emitting loop's budget parameter must bound **all startup work, fuel computation, and a full round**; it is not required to equal the smaller tableau horizon `T`. No `O_M(T²)` runtime claim follows merely from the output-length calculation.

   For the old empty-language counterexample, every input still receives its Cook–Levin tableau. The reference rejection bit is suppressed; the final word is the unsatisfiable tableau's serialization. There is no parser-failure route to the satisfiable empty CNF, no leaked `[false]` prefix, and no physical halt at the reference verdict.

   This certifies customer fit at the inherited statement/construction granularity. The actual record producers, embeddings, startup/round proofs, and explicit polynomial coefficients remain the designated fill obligations. The mapping no longer omits an independent semantic contract or requires a stronger public bridge.

4. **NOTE — R2-3 is closed, and the earlier closed emitter findings remain closed.**

   **Location:** `machine-library-design.md:500–505`, with §11b item 6. The explicit inline supersession marker now appears immediately after the historical private-`constTM` claim. It gives the correct alternatives: direct finite-control emission for fixed words and `exists_emitCallTM` for computed chunks. This is the requested repair while preserving the historical text.

   Reverse-patch comparison confirms that this round changes no other executable Build code beyond the two positive-tape conjuncts. The forwarding-host sketch, new prefix-summation requirement, unary-token separating example, grammar-state distinction, and definition documentation therefore retain their round-2 dispositions. The 3B normalization and 4B validation/dualization assessments remain in force; neither inherits the withdrawn 4A parser-fallback rule.

5. **NOTE — Mechanical evidence is strongly corroborated; execution and integration-history claims retain explicit limits.**

   **Locations:** the three `audits/evidence/emitter-infra/*.patch` files; round-3 logs; closure and lint programs; both batch-A REPORTs; the 57-module order list.

   | Maintainer attestation | Independent result and limit |
   |---|---|
   | 1. A-continuation: 69 helpers, no new admissions, preservation/replay, base-hash erratum | The attached `Nondeterminism.lean` matches the continuation REPORT exactly: 4,407 lines, 229,682 bytes, SHA-256 `2198f269b70c70f329b095c63c06b4b4d5adb9656fceed807dfab14c6ee3ba79`. Its 69 new private names match the REPORT's list in order; their source block contains no `sorry`, `axiom`, or `unsafe`. Removing that block and its continuation appendix reconstructs the earlier REPORT's exact source hash, as detailed below. The second shipped source `EXP.lean`, the continuation's kernel-closure program/log, integration replay artifacts, and the maintainer's erratum decision-log entry are not attached. Their stronger execution/history assertions are not independently reproduced here. |
   | 2. Fresh 57/57 sweep, zero errors, 20 admissions | The attached log has 57 distinct `CHECK` entries in the exact supplied module order, zero `error:` lines, 20 admission warnings, and `FULL_SWEEP_COMPLETE`. Its warning split is 13 campaign + 7 Build. The four Build sources contain exactly seven comment-stripped `sorry` sites: Loop 3, Wrappers 1, Primitives 3, Convention 0. Fresh compilation/olean production against these precise bytes was not rerun. |
   | 3. Full closure regression, unchanged expectations | All 18 expected name/root-list pairs from the attached program occur in order: 17 empty lists and the expected self-root for `EXP_subset_NEXP`; the log reports exit zero. The program traverses checked declaration types/opaque values and inductive constructors, checks admission roots, and constrains axioms. These are regression checks, not an audit of all 69 new helpers' kernel closures. The log identifies `96d5b017ebcf69ff0c0eef4959e5c7d9141dfa20 + working-tree r3 repairs`; final-commit checked-byte linkage remains a maintainer attestation. |
   | 4. Pinned repair scope | Patch `22d3d6bdd34b27704db62b3bcf7f29a932ffd3ff` has 92 insertions and 4 deletions over three files. Reverse application succeeds for both supplied changed files, Loop and the design document; both preimages and postimages match the patch's blob-hash prefixes. After removing comments/whitespace, deleting exactly the two added `0 < C.k ∧` fragments restores the preceding Loop code exactly. The unattached Chapter-1 plan change is a decision-log row visible in the patch; its complete file hash cannot be checked. |
   | 5. Build lint: 0 FAIL / 2 WARN | Independently ran the supplied lint program against all four extracted Build files. Exit zero, 0 FAIL / 2 WARN, with output byte-identical to the attached log. |

   The continuation predecessor reconstruction is especially informative: the resulting file has 3,013 lines, 157,403 bytes, and SHA-256 `deed194fd5abc2d7b10ad64306d952a669c860b278bb5f87f1a8558c14905c22`, exactly the earlier batch-A REPORT's hash. Its diff to the delivered continuation is precisely **1,395 insertions and one deletion**. The deleted line is the old docstring tail, `dependent on sorryAx; no complete target closure is claimed. -/` (with `sorryAx` backticked in the source); its prose is preserved before the appended continuation paragraph. The entire suffix from `theorem ntime_expPow_subset_NEXP` is byte-identical. This corroborates preservation of the five admissions in the supplied owned file, without claiming verification of the unattached sixth target or the integration's Git history.

   Continuing the reverse reconstruction through the round-2 and original spec patches also succeeds for every applicable supplied Build/design file. All applicable pre/post blob prefixes match. Their measured totals remain **1,676 insertions / 13 deletions** and **1,467 insertions / 0 deletions**, respectively. These checks authenticate consistency of the supplied file bytes and patch indices; they do not independently authenticate the patch headers as Git commit objects.

   The two previously missing evidence items are now present: the original phase-4 boundary-check table and the continuation REPORT/full source. Finding 1 is the resulting attribution correction, not a renewed claim that those attachments are missing. No observed compiler or regression failure is inferred from the remaining execution limits.

**Gate disposition:** both cumulative majors and the carried minor are discharged. The zero-blocker/major condition is satisfied. Correct the nonblocking provenance attribution in the next design/resolution update; preserve the six-stage boundary table in the 4A brief. This verdict authorizes treating the emitter interface/customer-fit audit as closed, not treating the seven admitted contracts or the partial continuation as completed proofs.

**Notation glossary.** Existing Lean identifiers retain their source meanings. `C` is the bridge module, `M` its fixed source machine, `arg` its tape argument, `f` the computed function, `x` the native input, and `hk` the exported positive-tape proof; `i₀` is its index-zero tape. In the bridge argument, `T` is the source runtime bound, `τ` the first source halt, `lo,hi` the visited interval endpoints, `w` its width (elsewhere an arbitrary word), `t_clear` and `t_call` the cleanup/call durations, and `K,c` fixed construction constants. `q` is a control state, `d` a configuration, `t` a time counter, `i` a tape/member/cursor index, and `j` a natural cell/iteration index. In the Cook–Levin argument, `n=|x|`, `Q(n)=C₀(n+1)^c₀` is exact certificate length, `m=n+Q(n)`, `T` the tableau horizon, `h` a source halt time, `k` the verifier's work-tape count, `B` the fixed snapshot-code width, `N=m+(T+1)B` the exclusive variable-index bound, `R` the final round index, `Gᵢ` the ordered member's clause list, `wᵢ` its emitted chunk, and `φₓ` the full CNF. In serializer formulas, `C` denotes a clause and `(v,b)` a literal's index and polarity. `++` denotes list concatenation, `[]` the empty list, `|·|` length, `w[j]?` optional lookup, `#` an occurrence count, and `O_M` a bound whose constant may depend on the fixed machine and encoding.
