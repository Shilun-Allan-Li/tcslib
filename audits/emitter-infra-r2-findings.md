**Gate: OPEN — 0 blockers, 2 majors, 1 minor.** The two cumulative major obligations are not discharged: the install bridge permits a zero-work-tape witness that stores no result, and the recorded 4A mapping does not implement the inherited Cook–Levin preparation stages. No false existence statement among the seven contracts was found. The intended log/undo construction is feasible, including with the positive-tape strengthening requested below. Round-1 findings 3–5 are closed.

Intended repository destination: `audits/emitter-infra-r2-findings.md`.
Audited bundle: `emitter-infra-r2-bundle.md`, SHA-256 `b10adf015b1feb689bffab8385644b7f19dbe105b1704d629f2f80d0de57e672`; exactly 31 attachment headers, matching the manifest. This is a statements/interface audit under the standing round-1 pack, not a proof fill or certification of the epoch-3 deliveries. References use repository paths and extracted-file line numbers. No supplied source or pack was modified. No Lean/Lake executable was available; the attachment set is not a buildable checkout. Mathematical construction arguments below are not claimed as kernel-checked proofs of the admissions.

| Cumulative item | Round-2 disposition |
|---|---|
| R1 finding 1 — clean-return/customer interface, major | **Open**, narrowed to the bridge's missing positive tape count (finding 1 below). The intended bridge construction and 3B normalization are feasible (findings 4–5). |
| R1 finding 2 — missing model/customer evidence, major | The main evidence omissions are supplied. **4A adequacy remains open**: the new mapping does not match the now-visible stage contract (finding 2). |
| R1 finding 3 — unchanged capturing-host sketch, minor | **Closed.** The new forwarding variant and new summation lemma are explicitly named. |
| R1 finding 4 — unary-token/marker confusion, minor | **Closed.** The corrected example and separate grammar-state handling match the definitions. |
| R1 finding 5 — per-declaration documentation, minor | **Closed.** The four definition comments and qualified seven-contract attestation now match. |
| R1 findings 6–9 — substantive positive assessments | Rechecked against the actual model/grammar definitions; retained, with the bridge-interface qualification below. |
| R1 finding 10 — attestations | Substantially strengthened by reversible patches, matching blob hashes, the full closure program/log, and independently reproduced lint; execution-provenance qualifications remain (finding 9). |

1. **MAJOR — The clean-call contracts do not guarantee that their argument/result tape exists. In particular, the install contract is vacuous as a data interface.**

   **Location:** `TCSlib/Complexity/TuringMachine/Build/Loop.lean`, `stateWord` (121), `exists_installCallTM` (2782), `exists_emitCallTM` (2811); `Finite.lean`, `FinTM`; `Simulation.lean`, `leftAction`/`rightAction` and configuration embeddings (162–198). **Cumulative:** R1 finding 1.

   Both new conclusions existentially choose `C : FinTM Bool` without `0 < C.k`. The bundled machine definition allows `C.k = 0`. But

   \[
   \mathrm{stateWord}\ 0\ a=\mathrm{stateWord}\ 0\ b
   \quad\text{for every }a,b,
   \]

   because both functions have empty domain `Fin 0`. Consequently, for any fixed native input and control state,

   \[
   \mathrm{Cfg.ofWords}\ q\ (\mathrm{stateWord}\ 0\ a)
   =\mathrm{Cfg.ofWords}\ q\ (\mathrm{stateWord}\ 0\ b).
   \]

   This is witnessed directly by function extensionality and `Fin.elim0`, or by the supplied `Cfg.ext_zero_tapes`.

   **Complete degeneracy witness.** Choose a zero-work-tape machine `C` with two states `entry` and `exit`. Every transition from `entry` stays on the native input cell, emits nothing, and changes the state to `exit`. Its work-action function is the unique function on `Fin 0`; the transition at `exit` can be a silent stationary self-loop. Then, for every native input `x`, argument `arg`, and function `f`,

   \[
   \begin{aligned}
   &C.\mathrm{tm.runFrom}
     (\mathrm{Cfg.ofWords}\ \mathrm{entry}\ (\mathrm{stateWord}\ 0\ \mathrm{arg}))\ 1\\
   &\qquad=\mathrm{Cfg.ofWords}\ \mathrm{exit}\ (\mathrm{stateWord}\ 0\ \mathrm{arg})
    =\mathrm{Cfg.ofWords}\ \mathrm{exit}\ (\mathrm{stateWord}\ 0\ (f\ \mathrm{arg})).
   \end{aligned}
   \]

   Take the contract's `c = 1` and `t = 1`. Its remaining obligations are

   \[
   1\le T(|\mathrm{arg}|)+|\mathrm{arg}|+|f(\mathrm{arg})|+1,
   \qquad 0<1,
   \qquad \neg\exists t'\in\mathbb N\;(0<t'<1),
   \]

   all true. Thus the entire install conclusion holds independently of `M` and `hM`, even for an arbitrary noncomputable `f`. This does **not** refute the existence theorem; it refutes the claim that its conclusion supplies an installed result for a caller.

   Padding does not repair this inference. With `C.k = 0`, all newly added host tapes are inactive tapes in `leftCfg`/`rightCfg`; their actions are `(none, 0)`. If a host places `arg` on such a tape and calls this witness for `f arg = arg ++ [true]`, that tape stays unchanged. At cell `arg.length`, its value is `none`, whereas the required result tape has `some true`. No result can be extracted from the advertised bridge contract.

   The emit bridge's physical output does prevent this degeneracy for nonconstant `f`: deterministic runs from the same zero-tape seam cannot emit different answers. However, a constant function permits zero tapes, so that contract still does not uniformly supply its promised tape-resident preserved argument. Its interface should expose the same tape guarantee.

   **Required repair:** add `0 < C.k` to both existential conclusions, or return a machine with tape count explicitly of the form `k + 1`. Then the actual index `⟨0, hk⟩` exists and the seam equality yields `bufferTape (f arg)` or `bufferTape arg` at that index. No change to `stateWord` or the audited loop contracts is needed. The log/undo route in finding 4 constructs this stronger interface. Choosing a positive-tape implementation privately, without exporting the fact, does not fix the public contract.

2. **MAJOR — The purported 4A stage mapping substitutes parser validation for Cook–Levin's five silent preparation stages, and leaves the required ordered chunk schedule unspecified.**

   **Location:** `machine-library-design.md` §11b item 3 (578–591); `TCSlib/Complexity/CookLevin/Hardness.lean`, `SAT_NPHard` sketch, especially stages (s1)–(s6) (159–206); `audits/ch2-phase4-findings.md`, finding 1 and Derivation C; `audits/ch2-phase4-resolutions.md` (39–69). **Cumulative:** the customer-fit part of R1 finding 2.

   The inherited stages are exact arithmetic; virtual reference input; intercepted simulation output/halt; the inclusive trajectory; greatest strictly earlier visits; and serialization. They are **not** parser-validation stages. Cook–Levin's source is an arbitrary language in `NP`; every binary word `x` is a legitimate source instance. There is no CNF well-formedness condition on `x`.

   Interpreted as validating native `x`, the proposed invalid-input fallback is incorrect. For example, take the empty source language and `x = []`. From the supplied definitions,

   \[
   \begin{aligned}
   &[]\notin\varnothing,\qquad \mathrm{CNF.parse}([])=\mathrm{none},\\
   &\mathrm{CNF.serialize}(\mathrm{CNF.fallback})
      =\mathrm{CNF.serialize}([])=[\mathrm{false}],\\
   &\mathrm{CNF.decode}([\mathrm{false}])=[]\text{ is satisfiable}.
   \end{aligned}
   \]

   Hence the literal validation/fallback route produces a SAT yes-instance for a source no-instance. The empty language is in `NP` (a constant rejecting verifier suffices). If the intended validation instead concerns *derived internal records*, those records and the reason they validate for **every** source input must be identified; §11b does neither. The parse-before-emission obligation belongs to the 3B and 4B decode-based transducers, not to validation of Cook–Levin's native source word.

   More generally, an emit call guarantees a clean call of an already specified transducer. It does not itself compute the exact horizon, virtual reference trajectory, or last-visit records. The following inherited obligations remain unmapped:

   | Required stage | What a correct bridge/loop mapping must retain |
   |---|---|
   | s1: exact arithmetic | Exact `Q(n)`, `m = n + Q(n)`, and `T`, with `x` retained and arithmetic answers captured; no enlargement of certificate length. |
   | s2–s3: reference simulation | Virtual input `false^m`, virtual head initially 1 with clamping to `0,…,m+1`; source writes/moves performed on the halting transition; source output suppressed and source halt made internal. |
   | s4: trajectory | Records at **all** times `0,…,T`; administrative transitions excluded from simulated time; frozen source positions recorded after early halt. |
   | s5: last visits | Greatest matching time **strictly below** the target; sequential-access comparison costs included. |
   | s6: emission | An explicit decomposition of the fixed, ordered clause families into chunks; exactly one final formula terminator; clean state update after each group. |

   There is also a count/order issue to settle, rather than merely calling `R` the snapshot bound. With `T+1` snapshot times, the six families have respectively

   \[
   n,\quad 1,\quad T,\quad T+1,\quad k(T+1),\quad T
   \]

   members. Thus “one group per round, `R = T`” needs a stated grouping of these families that covers pinning and acceptance and preserves the promised serialization order. A time-major interleaving is not automatically the same serialized word as the fixed family order.

   **Required repair:** replace item 3 with a real stage-to-seam mapping. One feasible choice is a silent startup that computes and packs the exact preparation records into `s0 x`, followed by a cursor over the ordered family-member list. With one family member per round, its length is

   \[
   n+1+T+(T+1)+k(T+1)+T=n+(k+3)T+k+2,
   \]

   so choose `R = n+(k+3)T+k+1`. Empty template outputs are allowed, but their rounds must still take positive time. Append the single final terminator to the last chunk. Alternatively, retain `R = T` and specify a different exact ordered partition into `T+1` chunks. Either choice has an input-length-only polynomial round count. Name how s1–s5 finish with empty physical output and a clean persistent word, using the positive-tape bridge from finding 1 where appropriate.

   The required length ledger is available and sound:

   \[
   |\mathrm{serialize}(\varphi_x)|
   =1+2\,\#\mathrm{clauses}
     +\sum_{(v,b)\text{ occurrence}}(v+3).
   \]

   In particular, the pinning contribution is

   \[
   \sum_{j=0}^{n-1}(j+5)=\frac{n(n-1)}2+5n.
   \]

   The inherited bounds `T ≥ (m+1)^2`, `n ≤ m`, and packed indices below `m+(T+1)B` make total output length `O_M(T²)`. Native scans and preparation may require a larger polynomial **time** bound. Merely saying that lengths sum does not identify the chunks or discharge the silent preparation stages.

   This finding does not reopen `SAT_NPHard` or the closed phase-4 statement gate. It rejects the new claim that §11b already maps that customer's inherited obligations. Decision 11.3 therefore still prevents closing the emitter adequacy gate for 4A.

3. **MINOR — The P17 correction is present in §11b but was not applied or cross-referenced at the location claimed to be corrected.**

   **Location:** `machine-library-design.md` §11a item 1 (500–502), §11b item 6 (604–610); round-2 pack repair 8.

   The new §11b rule is feasible: emit a fixed finite word directly with body control, and use the clean emit call for computed unbounded chunks. But §11a still literally says `emitPhase` applied to the private P2 `constTM`, while §11b says that §11a “is corrected accordingly.” The pinned repair patch only appends to this document; it does not change that earlier line.

   **Repair:** mark §11a item 1 explicitly superseded by §11b item 6, or replace its rule with the corrected rule. If preserving historical text is intentional, say that the later record supersedes it instead of claiming a textual correction. This is documentation drift, not an additional construction obstruction. `Turing.FinTM.emitAction` and its fixed-word emission lemmas in `Simulation.lean` (88–138) provide public finite-control vocabulary; the private constant machine need not be exposed.

4. **NOTE — The substantive positive-tape bridge construction survives the log/undo audit, including arbitrary native input and the stated envelope.**

   **Location:** the two new bridge statements/sketches; `Configuration.lean`, `Action.apply` (203); `Simulation.lean`, `bufferTape`, `VirtualTag`, `virtualMove_correct` (494–611); `Build/Wrappers.lean`, capture/forwarding vocabulary.

   Here is a construction-level justification independent of the missing A-continuation proof source. Reserve a genuine argument tape and disjoint source-work, virtual-input, capture, and history tapes. Keep the **native** input head at 1 and ignore its symbol throughout. Copy `arg` to the virtual-input tape. The existing virtual-input representation uses work-head position `p−1` for native virtual position `p`, with the boundary tag resolving the two blanks; for the empty word, initial position 1 is the right boundary and the initial tag is `true`.

   For each simulated source transition, store a fixed-width history record containing the old source state/tag, old scanned source-work symbols, source-work moves, and the **actual clamped virtual-input displacement**. The source machine is fixed and finite, so this record has constant size depending only on `M`. Recording a requested outward input move instead of its clamped displacement would be wrong. Execute all effects, including a write, move, and emission on a transition whose successor is halted. Capture emitted bits separately. Stop simulation at its first halt; do not run for a computed value of the potentially noncomputable bound `T`.

   The undo step is local. For one source tape, write `h_j` for its head and `w_j` for its contents before source step `j`; let `d_j` be the recorded move. `Action.apply` gives

   \[
   h_{j+1}=h_j+d_j,
   \qquad
   w_{j+1}(z)=
   \begin{cases}
   a_j.\mathrm{write}.\mathrm{getD}(w_j(h_j)),&z=h_j,\\
   w_j(z),&z\ne h_j.
   \end{cases}
   \]

   Undo first moves back to `h_{j+1}−d_j=h_j`, then restores the logged symbol `w_j(h_j)`. At `z=h_j` this restores the old symbol; at every other cell the forward step and the undo step leave `w_j(z)` unchanged. Thus the entire tape is exactly `w_j`. This includes `some none` erasures and outer-`none` no-writes. Restore the recorded virtual displacement and tag similarly. Reverse induction over the history restores blank source scratch and all source heads to their initial positions. The captured result is excluded from this reversal and remains available.

   If the first halt takes `τ` source steps, the timed computation and absorption imply

   \[
   1\le\tau\le T(|\mathrm{arg}|),\qquad
   \mathrm{captured}=f(\mathrm{arg}),\qquad |f(\mathrm{arg})|\le\tau.
   \]

   History has constant length per source step. Writing, reading, and erasing it costs a constant times `τ`; undo follows the recorded head paths and needs no random access or search for nonblank cells. In install mode erase the old argument and copy the captured result to tape 0. In emit mode replay the captured result while retaining the original argument. Erase temporary words and restore their heads; use a fresh exit control state reached only after cleanup. These operations also cover empty arguments/results.

   For fixed construction constants `K₁,…,K₅`, the total is bounded by

   \[
   \begin{aligned}
   &K_1(|\mathrm{arg}|+1)+K_2\tau+K_3\tau
       +K_4(|\mathrm{arg}|+|f(\mathrm{arg})|+1)+K_5\\
   &\quad\le(K_1+K_2+K_3+K_4+K_5)
       \bigl(T(|\mathrm{arg}|)+|\mathrm{arg}|+|f(\mathrm{arg})|+1\bigr).
   \end{aligned}
   \]

   There is no cost depending on `|x|`: the native input is never scanned. No monotonicity or computability of `T` is used. The output-size term is sufficient for install/replay and is also bounded by the source run. Positivity and first-positive-exit discipline are obtained by the disjoint phase controls.

   With positive tape count exported, `leftAction`/`rightAction` preserve arbitrary inactive host tapes, so callers can retain other tuple fields outside the call's active tape block. First-exit interception may need the same one-step release flag used by the existing loop machinery if a supplied module has `entry = exit`; distinct entry/exit need not be a new theorem hypothesis. Output-prefix commutation extends both clean-call equations to accumulated physical output. These facts make the strengthened contracts adequate normalizing interfaces; they do not supply the customer's parsing/arithmetic algorithm automatically.

5. **NOTE — The 3B normalization is feasible against the actual `satRedTM` table; its remaining generic interface defect is finding 1.**

   **Location:** `ClassNP/SAT.lean`, `satChain`/`satSplitClause` (1365–1376), `satReduction_*` (1657–1800), `satRedTM` (1834–1897), `satRed_start` (2299); §11b item 2; batch-B report's continuation frontier.

   The table confirms both the earlier obstruction and a feasible normalization. States 0–1 install the marker at −1; states 2–8 perform the silent maximum pass and rewind; states 17–21 buffer an entire prospective third literal, including polarity, before testing whether another literal follows; states 22–32 emit a fresh positive/negative pair and increment the unary cursor; states 33–34 erase/replay the buffer and find the permanent marker. The raw state-9 endpoint is still not `ofWords`.

   A normalized round can encompass a complete literal and its lookahead, so **no literal buffer has to cross a seam**. Store the unary fresh cursor, consumed-prefix length, and one of the finite grammar phases in the state word. Starting from a clean seam, re-find the consumed position on native input, do that round's work with a temporary buffer, and erase/rewind it before returning. A round-local marker may be erased at completion; alternatively preserve a temporary length/path record. The permanent marker is unnecessary. The maximum-pass argument can be reused with its marker omitted or subsequently erased and its result packed into the new state word; the literal `satRed_start` endpoint is not itself the new startup equation.

   A concrete normalized schedule is:

   | Phase and next valid input item | Chunk and next phase |
   |---|---|
   | Formula level, clause marker `true` | Emit `true`; enter first-literal phase. |
   | Formula level, formula terminator `false` | Emit `false`; enter finished phase. |
   | First-/second-literal phase, literal | Emit its complete serialization; advance the phase. After the second literal, enter tail phase. |
   | Any clause phase, clause terminator `false` | Emit `false`; return to formula level. |
   | Tail phase, literal `ℓ` with another literal following | Emit `serializeLit (j,true) ++ [false,true] ++ serializeLit (j,false) ++ serializeLit ℓ`; increment cursor `j`; remain in tail phase. |
   | Tail phase, last literal `ℓ` | Emit `serializeLit ℓ`; the next round consumes the clause terminator. |
   | Finished | Take a positive silent round, preserve state, emit `[]`. |

   The tail rule is precisely the serialization of the `satChain` recurrence: after the first two literals it closes `[head,b,(j,true)]`, opens the next clause with `(j,false)`, and resumes with the buffered original literal. Induction on the remaining literals gives `satSplitClause`; induction on the clause list threads its fresh cursor and gives `satTransformFrom`. Empty clauses and the empty formula follow the marker/terminator rows. This is the needed output-identity argument; `satReduction_correct` alone would not prove that a candidate machine emits `satReduction`.

   Complete validation, including **trailing data**, remains necessary before the first emitted clause marker. The batch-B plan already names the proved `satSyntax` guard/canonicalizer. It must be retained: on malformed input use `satReduction_fallback` and emit `[false]`. One may use the outer conditional/canonicalizer, or give the total loop an invalid-input phase whose first round emits `[false]` and then becomes finished. The latter also handles `x=[]`, for which `R=0` gives exactly one round. A unary-token split by itself is not a whole-string validator.

   On a valid input of length `n`, each nonfinished round consumes at least one bit. Therefore the formula terminator is processed within `n` such rounds; `R(n)=n` gives `n+1` total rounds, with empty padding after completion. The phase invariant includes finished states and is step-closed. A return dispatcher can ensure positive duration even for empty chunks.

   The banked cursor bounds give `j ≤ 2n`. An original literal index `v` is at most `n`, and `|serializeLit(v,b)|=v+3`. Hence the largest displayed fresh-fragment chunk has length

   \[
   (j+3)+2+(j+3)+(v+3)=2j+v+11\le5n+11.
   \]

   Arguments assembled from the cursor, offset, finite tag, and remaining input have length `O(n)` under unary counters and fixed-depth pairing. Catalog token splitting, pair projections, append, and the strengthened clean calls therefore admit a common input-length-only polynomial round envelope; startup and fuel computation can be included in the same envelope. In §11b, “token-bounded” should be understood as an input-length bound such as this one, **not** a bound by the next original token alone: a short token can trigger emission of a large fresh index.

   Independent finite corroboration: a Python transcription of all 35 transitions and of the normalized rounds agreed with the pure formula transform on 5,908 valid formulas, including widths through six, multiple clauses, both polarities, empty cases, and large prior indices followed by short literals. This is supporting evidence only; it is neither a Lean proof nor a general correctness claim for the unfilled raw machine.

6. **NOTE — 4B's all-string validation/dualization fits the emitter interface; it is the appropriate customer for the parser/fallback part of §11b.**

   **Location:** `Formulas/CNFEncoding.lean`, serialization/parse/decode (88–158); `Formulas/DNF.lean`; `ClassNP/Tautology.lean`, `TAUTOLOGY_coNPComplete` sketch (1256–1276).

   The target transducer is `serialize (dual (decode x))`. On a successful complete parse, the representation theorem and serializer definitions let it copy all clause markers, unary indices, and delimiters while flipping exactly each literal's polarity bit. Output length then equals input length. On failed parsing it must output `serialize [] = [false]`, of length one, with no earlier leaked prefix. A complete decision prefix followed by a valid scanner or a fixed fallback branch is therefore the right architecture here.

   The fallback is consistent with the reduction: malformed input decodes to the satisfiable empty CNF; its empty DNF dual is not a tautology. A grammar-state/offset loop with an absorbing finished phase has the same round-count and clean-return discipline as in finding 5. No additional configuration-level conclusion for the **outer** emitting loop is forced by this customer's final function-level target. The generic clean-call repair still needs finding 1's positive tape guarantee wherever its stored argument/result is used.

7. **NOTE — The model-level re-derivations validate the unchanged emitting-loop and forwarding statements; the corrected host sketch closes R1 finding 3.**

   **Location:** `Configuration.lean`, `moveInputPos`, `Cfg.inputSymbol`, `Action.apply`; `Deterministic.lean`, `step`/`runFrom`; `Build/Wrappers.lean`, `emitAction`, `emitCfg`, `emit_run`; `Build/Loop.lean`, `exists_emitLoopTM` and its host ledger.

   Let `P_p(c)` replace a configuration's output by `p ++ c.output`. Input symbol, work symbols, and control are unchanged. In a live configuration the same action is selected; its input clamping has the same arguments. Output associativity gives

   \[
   (p\mathbin{++}c.\mathrm{output})\mathbin{++}a.\mathrm{output.toList}
   =p\mathbin{++}(c.\mathrm{output}\mathbin{++}a.\mathrm{output.toList}).
   \]

   In a halted configuration both steps are identities. Thus, by componentwise equality and induction,

   \[
   \mathrm{step}(P_p(c))=P_p(\mathrm{step}(c)),\qquad
   \mathrm{runFrom}(P_p(c),t)=P_p(\mathrm{runFrom}(c,t)).
   \]

   Similarly, every step adds zero or one output bit, including the action whose successor is halted. Induction gives

   \[
   |(\mathrm{runFrom}(c,t)).\mathrm{output}|\le|c.\mathrm{output}|+t.
   \]

   Substituting a clean round seam proves `|emitF x s| ≤ t ≤ T(|x|)`. No emission-size hypothesis is missing. `hInv0` and `hInvStep` cover every orbit state, and a live round endpoint excludes an earlier halt by absorption. Positive duration and strict-interior anchor exclusion identify the first positive return. The zero-tape case is harmless for **this** theorem: the actual output equation still forces the emitted chunk, unlike install mode in finding 1.

   The forwarding action/configuration satisfy

   \[
   (\mathrm{emitAction}\ \mathrm{emb}\ \mathrm{ret}\ a).\mathrm{apply}
       (\mathrm{emitCfg}\ \mathrm{emb}\ \mathrm{ret}\ p\ c)
   =\mathrm{emitCfg}\ \mathrm{emb}\ \mathrm{ret}\ p\ (a.\mathrm{apply}\ c).
   \]

   The state on either side is `some ((a.state.map emb).getD ret)` and the output equality is associativity. A halting action's last bit is therefore forwarded. The `hlive` guard supplies each source step before time `t`; it does not require the time-`t` endpoint to be live. At `t=0` the equation is reflexive. For a timed function witness, use its actual first halt before invoking this guarded lemma. Embedding collisions do not invalidate the conditional identity because `hagree` already imposes transition consistency.

   The new docstring correctly calls for a **different forwarding host** and a new prefix-summation lemma. The one-state self-emitting counterexample still refutes the old capture host, but no longer refutes the stated construction plan. Silent startup cannot have emitted earlier because its final output is empty and output only grows. Silent countdown preserves all accumulated chunks. With counter initialized to `R(n)`, round zero precedes the first debit and the zero-counter round precedes underflow; indices are exactly `0,…,R(n)`, including one round at `R=0`.

   Finally, let `L = |Nat.bits(R(n))| ≤ T(n)`. Reusing the controller ledger with forwarded body output gives

   \[
   \begin{aligned}
   \mathrm{startup}&\le5T(n)+7+T(n)+2\le10(T(n)+1),\\
   \mathrm{one\ round}&\le T(n)+1+2L+4
       \le3T(n)+5\le10(T(n)+1),\\
   \mathrm{total}&\le10(T(n)+1)(R(n)+2).
   \end{aligned}
   \]

   Input rewind is charged to actual preceding displacement, not to a full input scan. No hidden `T(n) ≥ n` assumption is needed. This verifies the construction budget, not a checked implementation of the new host.

8. **NOTE — The original stream/split contracts and the remaining documentation repairs retain their round-1 verdicts.**

   **Location:** `Build/Convention.lean`, `solveSplitWith` and `unaryTokenSplit`; `Build/Primitives.lean`, the three emitter-increment contracts; corrected definition docstrings in `Build/Wrappers.lean`.

   The unary splitter consumes a maximal true-run and its false delimiter, when present; it is not a standalone-true-marker reader. The separating example is now stated correctly. On a serialized literal the token contains `v+1` true bits plus its delimiter; polarity is the following independent bit. Empty and unterminated inputs retain their declared pure-function semantics rather than claiming successful CNF parsing. Token and remainder concatenate to the input, so

   \[
   |\mathrm{pairEncode}(\mathrm{tok},\mathrm{rest})|
   =2|\mathrm{tok}|+2+|\mathrm{rest}|\le2|x|+2.
   \]

   A streaming encoder therefore fits a fixed linear budget; append-bit takes `|x|+1` transitions by copying and emitting the extra bit on the final halt. These true function contracts acquire a usable persistent-word interpretation only through a nondegenerate clean-call interface.

   For width-parametric split search, each candidate satisfies `i ≤ n`; evaluating the exact candidate-length input costs at most `TE(i) ≤ TE(n+1)`. Whole canonical binary-word equality gives

   \[
   \mathrm{Nat.bits}(f(i))=\mathrm{Nat.bits}(n-i)
   \iff f(i)=n-i
   \iff i+f(i)=n.
   \]

   Scan candidates in increasing order, capture through the actual halt, clean by elapsed-time accounting, and stop at the first equality. No monotonicity of `f` is needed. With a constant `K`, the total including preparation is bounded by

   \[
   K(n+2)(\mathrm{TE}(n+1)+n+2)
   \le2K(n+1)(\mathrm{TE}(n+1)+n+2).
   \]

   The `n=0, f(0)=0` case emits the nonempty encoding of the empty pair; failed search emits `[]`. The polynomial specialization is definitional, and the exponential evaluator's monotone polynomial bit-time bound remains suitable. This still does not replace the independent A continuation's bespoke configuration-level body proof with a final-function assertion.

   All four definitions now have the promised customers/construction notes, and all seven new contracts have the qualified spec documentation. Thus R1 findings 4 and 5 close. The public fixed-word emission vocabulary makes P17's corrected construction feasible; only the stale cross-reference in finding 3 remains.

9. **NOTE — The pinned changes and mechanical attestations are corroborated; compilation and the cited continuation provenance remain execution/source limitations.**

   **Location:** both `audits/evidence/emitter-infra/*.patch` attachments; round-2 logs; `audits/programs/ch2-e2-ClosureAxioms.lean`; `scripts/style_lint.py`; 57-module order list.

   | Attestation | Independent result |
   |---|---|
   | 1. Sweep: 57/57, zero errors, 20 admissions | The log has exactly 57 distinct `CHECK` entries in the supplied order, no `error:` lines, 20 admission warnings, and the completion marker. The split is 13 campaign + 7 Build. Comment-stripped Build sources contain exactly 7 `sorry` sites: Loop 3, Wrappers 1, Primitives 3, Convention 0. |
   | 2. Full closure regression prints | All 18 expected root lists in the attached program occur in the log, in order: 17 empty lists and the expected self-root of `EXP_subset_NEXP`; reported exit is zero. The program checks checked-kernel declaration types/opaque values, constructors, admission roots, and the allowed axiom set. The previous truncated-log limitation is removed. |
   | 3. Both pinned spec diffs / preservation | Patch `883ebc79d186cf8b8a30c31c8e1b2e2379ef5147` has exactly **1,467 insertions, 0 deletions**. Patch `175fbc0549d3a017478584903793b7b78a0f14da` has **1,676 insertions, 13 deletions**; the 13 removed lines are emitter-new documentation, not pre-increment declarations. See reconstruction below. |
   | 4. Lint: 0 FAIL / 2 WARN | Independently ran the supplied program on the extracted four Build files. Exit zero; output matches the attached log byte-for-byte, including the two Loop/Primitives size warnings. |

   In scratch copies, reversing the repair patch and then the original spec patch succeeded for all four Build files and the design document. Every applicable reconstructed preimage matches its patch's Git blob-hash prefix; attached repaired postimages also match their patch indices. Removing only the two newly added bridge declarations leaves the repaired Build code identical to the round-1 code after comments/whitespace are removed. The original patch inserts declarations only at the new blocks and deletes no prior text. This substantiates the claimed preservation of the pre-emitter library, rather than inferring preservation from a current snapshot. The attached `SAT.lean` also matches the batch-B report's full SHA-256 exactly.

   These checks establish consistency of the supplied diffs, files, and logs; the patch headers are not independently authenticated Git commit objects. The sweep's fresh output-directory execution and its precise checked-byte linkage were not reproduced. The closure log identifies `5920721ff0224260a692a950fba8221c5eeda8cf + working-tree r2 repairs`, not the final repair commit, so it remains a maintainer execution attestation even though all expected root outputs are now visible. No failure or regression is inferred from that qualification.

   Two narrower evidence limitations also remain. The attached batch-A report is the earlier partial frontier, not the later A-continuation log/undo source: it does not substantiate the new “proved in-file pattern” attribution. The phase-4 resolutions describe the second-round boundary-check table, but `ch2-phase4-reaudit-findings.md` containing that table is not an attachment. The actual six-stage contract, model, and main serialization derivation **are** attached and sufficient to identify finding 2 and to re-derive the relevant boundaries. If the 4A brief must inherit that second-round table verbatim, provide the original table with its handoff. These limitations are not additional major findings against the truth of the bridge statements.

**Gate-closing changes required:** expose a positive work-tape count in both bridges; replace §11b's 4A paragraph with the actual silent-preparation and ordered-round mapping; resolve the minor P17 supersession wording. Ordinary native-machine proofs remain fill work. The present audit does not authorize treating either outstanding adequacy obligation as discharged merely because a stronger implementation could later be chosen.

**Notation.** Existing Lean identifiers retain their source meanings. `++` is list concatenation; `[]` is the empty list; `|w|` is word length; `#` denotes a count. `C` is the bridge module; `M` is a fixed source machine; `arg` is its tape argument, `f` its computed function, and `x` the native input. `c`, `K`, and `K₁,…,K₅` are fixed construction constants; `t,t'` are transition counts; `τ` is the source's first halting time. In the undo equations, `j` is source-step index, `a_j` its action, `h_j` its work-head position, `w_j` its work-tape contents, `d_j` its move, and `z` a tape cell. In the customer/ledger discussion, `n=|x|`, `Q(n)` is the exact certificate length, `m=n+Q(n)`, `T` is the Cook–Levin horizon, `k` the verifier's work-tape count, `B` the fixed snapshot-code width, and `φ_x` the assembled CNF; `false^m` is a list of `m` false bits and `O_M` permits constants depending on `M`. In the separate 3B calculation, `j` is the fresh-variable cursor, `ℓ` a literal, `v` its index, and `b` its polarity. In the loop/primitive discussion, `T(n)` is the loop budget, `R(n)` its initial counter, `L` its binary width, `P_p` prefixes output by word `p`, `c` in `P_p(c)` denotes a configuration, `a` an action, `TE` the evaluator budget, and `i` a candidate index. `tok` and `rest` are the unary split's token and remainder.
