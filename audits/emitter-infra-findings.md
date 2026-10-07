**Gate: OPEN — 0 blockers, 2 majors, 3 minors.** No false statement among the five new contracts was found. Their mathematical realizations are credible under the machine semantics used by the attached, previously proved library. The advertised customer coverage is not yet established: the return-configuration interface needs an explicit resolution, and the mandatory phase-4 evidence is absent.

Audited the supplied `emitter-infra-bundle.md`, SHA-256 `3f9d7fe76067e78272c3be86e8957256c8acb28adb31ac33418373a4f3ce6a77`. Its 14 attachment headers exactly match the manifest. References below use repository paths and declaration names; line numbers are within the extracted attachments. This is a statements/interface audit, not a proof fill or certification of the epoch-3 reports. No Lean or Lake executable was available, and the attachment set is not a buildable checkout. The pack and supplied sources were not modified.

1. **MAJOR — The claimed customer reuse still lacks an interface that establishes the required return configuration.**

   **Files/declarations:** `TCSlib/Complexity/TuringMachine/Build/Loop.lean`, `Turing.FinTM.exists_emitLoopTM` (2723); `Build/Wrappers.lean`, `Turing.emit_run` and `Turing.emitCfg` (249, 226); `Build/Primitives.lean`, `computesFunInTime_unaryToken` and `computesFunInTime_appendBit` (4459, 4475); `machine-library-design.md`, §11 E3′ and §11a items 1, 2, 4. Customer evidence: `audits/ch2-epoch3-agent-reports/batchB.md`, “Exact machine continuation frontier.”

   The emitting loop demands a concrete body whose round ends with all of the following: live control at `anchor`, native input head at 1, state word on tape 0 with head 0, every other body tape completely blank with head 0, and precisely the declared chunk on the output. In contrast, the two primitive contracts constrain only halting time and completed output from the genuine initial configuration. They say nothing about the final input head or source work tapes.

   The forwarding wrapper does not close this difference. Its conclusion preserves the source's actual terminal tapes and heads; it does not normalize them. In particular,

   \[
   \operatorname{emitCfg}(\mathrm{emb},\mathrm{ret},p,c).\mathrm{workTapes}
      =c.\mathrm{workTapes},\qquad
   \operatorname{emitCfg}(\mathrm{emb},\mathrm{ret},p,c).\mathrm{inputPos}
      =c.\mathrm{inputPos}.
   \]

   This is a logical interface issue, not merely an unfilled proof. A machine satisfying either function contract may write `true` on an extra scratch tape and move that head on its final halting transition, without changing its output or asymptotic budget. It still satisfies the contract. Its `emitCfg` image fails the clean-return equation. Thus that equation cannot be inferred for a witness using only the advertised function contract and forwarding lemma.

   There are two additional data-flow obligations. `emit_run` uses the same `input` for source and host; calling a primitive on the current state word rather than on the original input requires a virtual-input preparation. Also, `appendBit` produces `s ++ [b]` on output, whereas persistence requires installing that word on tape 0. Forwarding emits it physically. Capturing it instead requires a subsequent copy/install/erase/rewind stage. The loop engine preserves a correctly returned state word; it does not construct that return.

   The supplied 3B frontier exhibits the mismatch concretely. `satRed_start` reaches state 9 with a permanent nonblank marker on the second tape at position −1. `Cfg.ofWords ... (stateWord 2 s)` requires the entire second tape to be blank. These configurations differ at that cell even before streaming begins. Cursor plus input position must also be encoded in the sole persistent word; the raw streaming input position cannot cross an `ofWords` seam. Later literal buffering adds another representation/cleanup obligation. This does **not** prove a normalized body impossible; it proves that the reported machine is not already the promised instantiation.

   P17 has a related visibility limitation: `Composition.lean`'s `constTM` is private, and its public `computesFunInTime_const` theorem does not expose the no-movement configuration contract. The existing public emission-chain vocabulary may discharge this small case, but §11a should identify that actual rule, rather than claim that an arbitrary constant-function witness provides it. A fixed finite-control word is feasible; an unbounded tape-dependent chunk is a separate transducer obligation.

   **Required resolution before the adequacy gate:** specify either a reusable prepared-input/clean-return bridge, or a concrete customer normalization construction with its full entry/exit contract. For 3B this must name the encoded cursor/position/control data, marker and buffer handling, positive first return, a polynomial round bound, and an absorbing finished state with empty later chunks. State how token output is decoded and how append output becomes the next state word. Ordinary proofs can follow at fill time; the interface and feasible construction cannot be deferred. No change to the mathematically sound function contracts is forced, and a configuration-level *conclusion for the outer emitter* alone would not repair this body-entry problem.

2. **MAJOR — The “complete bundle” does not contain evidence needed for the required model and phase-4 customer checks.**

   **Files/declarations:** the immutable audit pack, “Evidence separation,” priorities 1, 2, 4, 6, and its verification appendix; `machine-library-design.md` §11a item 4; `Turing.FinTM.exists_emitLoopTM`, `Turing.emit_run`, and the customer-use claims on `computesFunInTime_unaryToken`.

   The manifest is arithmetically correct: there are 14 attachments. Its scope is insufficient for the promised audit. In particular, it omits the `audits/ch2-phase4-*` records containing the six-stage silence obligations and exact serialization ledger. It also omits the relevant Cook-Levin customer declarations and the CNF serialization/parser definitions. The 3B report describes its frontier but does not include `satRedTM`'s transition table; the 4B grammar is not supplied at all.

   The two files labeled “model files” are `Finite.lean` and `Composition.lean`. They import, but do not define, `MultiTapeTM.step`, `Action.apply`, the configuration/input-boundary machinery, and the `leftAction`/`rightCfg` simulation vocabulary. Those definitions reside in omitted dependencies, including `Configuration.lean`, `Deterministic.lean`, and `Simulation.lean`. The attached proved lemmas give substantial evidence about their behavior, used in findings 6–9, but that is not the requested inspection of their actual definitions.

   The claim “the final customer asks only for `PolyTimeComputable`, therefore a function-level emitter suffices” does not settle a possibly frozen intermediate stage contract. A function-level specification permits a machine to delay all output until its last phase; another machine can emit the same word earlier. Their final function and time bounds may agree while their stage configurations differ. Whether 4A requires those configurations, and how the exact ledger aligns with `R+1` rounds and the final serialization delimiter, cannot be decided from a reference to missing records.

   **Required resolution:** attach a pinned evidence addendum with the phase-4 contracts/ledger, relevant customer grammar and source interfaces, and the omitted model/simulation definitions. Give a stage-to-library mapping, including all-string validation before irreversible emission, the logical round count, and serialization terminators. Preserve the sent pack and record this omission in the resolutions file. This finding does not assert that the unavailable 4A/4B constructions are wrong; it prevents their coverage from being certified now.

3. **MINOR — The unchanged find-mode host is not an emitting-loop implementation.**

   **File/declarations:** `TCSlib/Complexity/TuringMachine/Build/Loop.lean`, construction sketch of `exists_emitLoopTM` (2716), and `loopHost` (762; body dispatch at 779–781, exhaustion at 826–827).

   `loopHost` calls the body through `captureAction`, whose physical output is always `none`. Only a genuine body halt dispatches to payload replay. An advancing body sets the false stop flag, takes the debit path, and eventually reaches a silent find-mode exhaustion. Output-prefix commutation preserves an existing physical prefix; it does not transfer the captured chunks to physical output.

   A minimal witness satisfies all the new hypotheses: use a zero-work-tape body whose sole state is the start/anchor and whose one-step self-loop emits `true` without moving; let `Inv` be true, `s0 x = []`, `stepF x s = s`, `emitF x s = [true]`, `R n = 0`, and `T n = 1`. The fuel machine halts silently in one step, computing `Nat.bits 0 = []`. Startup has duration 0; each round has duration 1 and satisfies strict-interior anchor exclusion. The required concatenation is `[true]`. The existing find-mode host captures that bit, then underflows and halts with physical output `[]`.

   This refutes the literal unchanged-host construction, **not the theorem**. A new host variant can forward the padded body actions with `emitAction`, leaving the fuel capture and silent countdown machinery intact. Its proofs must use configurations with arbitrary accumulated output. Alternatively, explicitly flush captured chunks with an accounted cost. Record the routing change in the sketch; re-proving a stronger contract for the unchanged host is impossible. Likewise, use a new prefix-summation lemma modeled on `loop_run`, not the frozen empty-output/Boolean `loop_run` itself.

4. **MINOR — `unaryTokenSplit` does not consume an arbitrary single-bit marker.**

   **File/declaration:** `TCSlib/Complexity/TuringMachine/Build/Convention.lean`, `Turing.unaryTokenSplit`, final docstring sentence (137–138); corresponding scanner use in `machine-library-design.md` §11 E3′.

   Direct reduction gives

   \[
   \operatorname{unaryTokenSplit}[\mathrm{true},\mathrm{false},\mathrm{true}]
     =([\mathrm{true},\mathrm{false}],[\mathrm{true}]).
   \]

   Consuming just the leading `true` marker would instead return `([true], [false,true])`. A unary value one has a two-bit terminated token `[true,false]`; it is not a single-bit `true` marker. A leading `false` is handled correctly as a one-bit zero token. State that this operation consumes unary tokens; identify separate grammar-state handling for standalone markers and polarity bits. The definition and its function-computation theorem remain true.

5. **MINOR — Maintainer attestation 4 overstates the per-declaration documentation.**

   **Files/declarations:** pack attestation 4; `Build/Convention.lean`, `solveSplitWith` and `unaryTokenSplit`; `Build/Wrappers.lean`, `emitAction` and `emitCfg`.

   All nine new declarations have descriptive prose and the spec-phase designation. The five contracts have construction sketches and named customers. The four definitions do not each carry both an explicit construction sketch and named customers; for example, `solveSplitWith` describes the equation and specialization but names no customer. The literal “every new declaration” assertion is therefore too strong. Qualify it to the five contracts, or add the missing documentation. The supplied lint summary of 0 FAIL / 2 WARN is not contradicted by this finding.

6. **NOTE — The emitting loop's clean-output premise, self-bounding emissions, invariant coverage, and round count survive the mathematical attacks.**

   **File/declaration:** `TCSlib/Complexity/TuringMachine/Build/Loop.lean`, `Turing.FinTM.exists_emitLoopTM`. Supporting attached declarations: `loop_output_length_le`, `loop_orbit_inv`, `loop_fuel_width`, `loopHost_prepare`, and `loopHost_reject`. Definition-level evidence limitation: finding 2.

   For a configuration `c`, write \(P_p(c)\) for the same configuration with output `p ++ c.output`. The transition semantics used by the attached proofs give

   \[
   (P_p(c)).\mathrm{inputSymbol}=c.\mathrm{inputSymbol},\quad
   (P_p(c)).\mathrm{workTapeSymbols}=c.\mathrm{workTapeSymbols},\quad
   (P_p(c)).\mathrm{state}=c.\mathrm{state}.
   \]

   In a live state the same transition is selected. Every non-output update is identical, including the input move: both executions have the same input word, input position, and move, so any boundary clamping has identical arguments. If the action emits the optional bit `a.output`, output associativity gives

   \[
   (p\mathbin{++}c.\mathrm{output})\mathbin{++}a.\mathrm{output.toList}
    =p\mathbin{++}(c.\mathrm{output}\mathbin{++}a.\mathrm{output.toList}).
   \]

   In a halted state both steps are identities. Thus one-step commutation and induction on time give

   \[
   \mathrm{step}(P_p(c))=P_p(\mathrm{step}(c)),\qquad
   \mathrm{runFrom}(P_p(c),t)=P_p(\mathrm{runFrom}(c,t)).
   \]

   Let \(s_i=(\mathrm{stepF}\ x)^{[i]}(\mathrm{s0}\ x)\), \(p_0=[]\), and \(p_{i+1}=p_i\mathbin{++}\mathrm{emitF}\ x\ s_i\). Induction from `hInv0` and `hInvStep` establishes `Inv x s_i` for every `i`, not merely the visited prefix. Applying `hround` and commutation takes the body seam with output \(p_i\) to the next seam with output \(p_{i+1}\). The empty-output hypotheses therefore do not require physically clearing accumulated output.

   The attached arbitrary-configuration bound is already the needed one:

   \[
   |(\mathrm{runFrom}(c,t)).\mathrm{output}|
      \le |c.\mathrm{output}|+t.
   \]

   At a clean seam this yields \(|\mathrm{emitF}\ x\ s|\le t\le T(|x|)\). It counts an emission on the action whose successor is halted; subsequent halted steps add nothing. Here the round endpoint itself is live, so an earlier halt is impossible by absorption. No additional emission-size premise is needed.

   Positive duration excludes the historical zero-step advance. Strict-interior anchor exclusion makes the endpoint the first positive return, while permitting the starting anchor. Startup's exclusion includes time 0 when startup is positive; zero-time startup is harmless. An empty invariant cannot make the premises vacuous because of `hInv0`. A zero fuel-time bound is also impossible by `FinTM.not_computesInTime_zero`. For zero body tapes, the encoded state word disappears, but deterministic first-return behavior still forces the same chunk for indistinguishable admissible seams; arbitrary noncomputable state data cannot evade that constraint.

   The counter begins with value `R |x|`, executes round 0 before debiting, and after round `i` continues exactly when `i < R |x|`. Round `R |x|` is executed before underflow. Hence the output indices are exactly `0,...,R |x|`, matching `List.range (R |x| + 1)`. At `R=0` there is one round, not zero. A customer with zero logical emission rounds must use an empty chunk or a separate zero-case branch.

   The budget also fits a forwarding variant. Put \(n=|x|\) and \(L=|\mathrm{Nat.bits}(R(n))|\le T(n)\). The attached controller ledger bounds fuel preparation by \(5T(n)+7\); body startup plus its stop/release costs at most \(T(n)+2\). An advancing round, including its stop and debit/underflow terminal, costs at most

   \[
   T(n)+1+(2L+4)\le 3T(n)+5\le10(T(n)+1).
   \]

   Startup is at most \(6T(n)+9\le10(T(n)+1)\). Consequently

   \[
   \mathrm{total}\le10(T(n)+1)+(R(n)+1)10(T(n)+1)
       =10(T(n)+1)(R(n)+2).
   \]

   This is an implementation ledger for the proposed forwarding variant, not a checked proof about the unchanged host. No hidden linear-in-input scan is needed: fuel rewind is charged to the actual fuel-run displacement, bounded by its time. Thus the statement does not silently require `T n ≥ n`.

7. **NOTE — `emit_run`, `emitAction`, and `emitCfg` have the correct lockstep shape, including the halting emission.**

   **File/declarations:** `TCSlib/Complexity/TuringMachine/Build/Wrappers.lean`, `Turing.emitAction`, `Turing.emitCfg`, `Turing.emit_run`.

   The componentwise identity to prove is

   \[
   (\mathrm{emitAction}\ \mathrm{emb}\ \mathrm{ret}\ a).\mathrm{apply}
      (\mathrm{emitCfg}\ \mathrm{emb}\ \mathrm{ret}\ p\ c)
   =\mathrm{emitCfg}\ \mathrm{emb}\ \mathrm{ret}\ p\ (a.\mathrm{apply}\ c).
   \]

   State equality follows because both sides use `some ((a.state.map emb).getD ret)`; the input/work updates coincide; the output equality is append associativity. In particular, `a.state = none` does not discard `a.output = some b`: the bit is appended and control becomes `some ret` on that same action.

   For a live source configuration, `hagree` converts this action identity into a step identity. At the induction step from time `u` to `u+1`, `hlive u` supplies precisely that liveness premise. At `t=0` the claimed run equation is reflexive, even if `c₀` is already halted. If `c₀` is halted and `t>0`, the guard is false at time 0. A source halting at time `t` is permitted; one that halted strictly earlier is excluded. A `ComputesFunInTime` upper bound must therefore first be cut to the actual first halt, rather than substituted blindly for `t`.

   Neither injectivity of `emb` nor disjointness of `ret` is needed for this conditional equality: `hagree` supplies transition consistency, and the guarded interval never steps beyond the source halt. Customers can use disjoint finite control for convenient phase separation.

   The same tape count is correct: forwarding needs no capture tape. To preserve unrelated host tapes, first pad/relocate the source with the existing block-embedding vocabulary, then apply the wrapper at the enlarged common tape count. This is compatible in shape with the attached uses of `leftCfg_run`/`rightCfg_run`; it does not supply the preparation and cleanup omitted in finding 1.

8. **NOTE — `splitSolveWith` has the right least-solution semantics and time envelope; its exponential instantiation is suitable at function level.**

   **Files/declarations:** `Build/Convention.lean`, `Turing.solveSplitWith`; `Build/Primitives.lean`, `Turing.FinTM.computesFunInTime_splitSolveWith`; `audits/ch2-epoch3-agent-reports/batchA.md`, `e3_exp_bits_timed` and the displayed body frontier.

   For original input length \(n\), enumerate candidates \(i=0,\ldots,n\). Prepare a virtual input of exactly length \(i\), run `E` to its first halt with captured output, and compare the entire canonical word `Nat.bits (f i)` with `Nat.bits (n-i)`. Then

   \[
   i\le n\ \Longrightarrow
   \Bigl[\mathrm{Nat.bits}(f(i))=\mathrm{Nat.bits}(n-i)
      \iff f(i)=n-i\iff i+f(i)=n\Bigr].
   \]

   Candidate preparation, suffix counting, and payload production take linear time in the original input length, up to machine constants. Evaluation, output comparison, and cleaning the evaluator's visited region take a constant multiple of its actual running time plus the linear overhead. A clean implementation can track visited intervals on auxiliary tapes; their extent is bounded by the elapsed evaluator run, without computing `TE` as a clock. For some fixed construction constant \(K\), each live round therefore fits

   \[
   K(\mathrm{TE}(i)+n+2)
      \le K(\mathrm{TE}(n+1)+n+2).
   \]

   Taking fuel `R n = n`, the loop envelope is a constant multiple of `(n+2)(TE(n+1)+n+2)`, hence of the stated `(n+1)(TE(n+1)+n+2)` because `n+2 ≤ 2(n+1)`. The length-`n+1` state can take a positive silent stall to close the invariant. Fuel computation and the final payload length `n+i+2 ≤ 2n+2` fit the same envelope.

   **Crucial implementation restriction:** execute `E` on the actual length-`i` prepared word. A generic composition bound evaluating `TE` at an inflated preparation-time bound would not imply the stated estimate for arbitrary monotone `TE`. Likewise, restoring only `O(n)` cells is not enough for an arbitrary evaluator; charge its whole visited region to its run time. These are feasible construction obligations, not missing assumptions on `f`.

   No monotonicity of `f` or `i+f i` is needed: search every candidate in order and stop only on equality. An oversized value at an early candidate does not license early failure. At `n=0`, there is one candidate. If `f 0=0`, both binary words are `[]` and the result is the nonempty `pairEncode [] []`; otherwise the result is `[]`. An empty captured binary word must be recognized through the evaluator's halt, not mistaken for failure.

   Specialization is definitionally exact:

   ```lean
   solveSplitWith (fun i => C * (i + 1) ^ e) n = solveSplit C e n
   -- rfl after unfolding the two definitions
   ```

   For the reported exponential evaluator, use \(f(i)=a\,2^{(i+1)^d}\) and \(\mathrm{TE}(m)=B(m+1)^{d+1}\). This budget is monotone. Since \(n+2\le2(n+1)\) and \(n+1\le(n+1)^{d+1}\), the new final bound is polynomial:

   \[
   \begin{aligned}
   c(n+1)\bigl(B(n+2)^{d+1}+n+2\bigr)
      &\le c(n+1)\bigl(B2^{d+1}(n+1)^{d+1}+2(n+1)^{d+1}\bigr)\\
      &=c\bigl(B2^{d+1}+2\bigr)(n+1)^{d+2}.
   \end{aligned}
   \]

   Thus the new theorem supplies the desired split *function* at a suitable budget, if its proof is filled. It does not itself produce the configuration-level body existential printed in the A report. The pack explicitly keeps that continuation bespoke and independent, so this distinction is not a new major against A. The harvest/template claim should retain that distinction; this audit does not certify the report's evaluator proofs.

9. **NOTE — The unary-token and append-bit function statements are true at the stated linear scale, including empty inputs.**

   **Files/declarations:** `Build/Convention.lean`, `unaryTokenSplit`; `Build/Primitives.lean`, `computesFunInTime_unaryToken`, `computesFunInTime_appendBit`.

   The recursive token definition has the advertised unary conventions:

   \[
   \begin{aligned}
   \mathrm{unaryTokenSplit}([])&=([],[]),\\
   \mathrm{unaryTokenSplit}(\mathrm{false}::r)&=([\mathrm{false}],r),\\
   \mathrm{unaryTokenSplit}(\mathrm{true}^m\mathbin{++}[\mathrm{false}]\mathbin{++}r)
      &=(\mathrm{true}^m\mathbin{++}[\mathrm{false}],r),\\
   \mathrm{unaryTokenSplit}(\mathrm{true}^m)&=(\mathrm{true}^m,[]).
   \end{aligned}
   \]

   Here `true` raised to a natural number means list replication, not a Boolean arithmetic operation. In every case `tok ++ rest = x`. Using the pairing length stated in the pack and realized by the attached primitive code,

   \[
   |\mathrm{pairEncode}(\mathrm{tok},\mathrm{rest})|
     =2|\mathrm{tok}|+2+|\mathrm{rest}|
     =n+|\mathrm{tok}|+2\le2n+2.
   \]

   A finite-state transducer doubles each token bit, including a present terminating `false`, emits the pair separator, then copies the remainder. On an unterminated token it emits the separator at the boundary without inventing a token delimiter. An implementation using at most two steps per token bit, one per remainder bit, and three final/control steps fits `2n+3 ≤ 3(n+1)`. Empty input consequently causes no output-length obstruction.

   For append-bit, copy each of the `n` input bits while moving right; on the right blank, emit `b` and halt. This takes `n+1` steps and outputs exactly `x ++ [b]`, including `x=[]`. Its input head is at the right boundary, illustrating why the true function statement does not also assert the clean return needed in finding 1.

   Neither vocabulary addition changes `incFixed`'s overflow convention. The polynomial specialization of `solveSplitWith` introduces no coefficient shift; the historical shift concerns the separate `certificateSplit` comparison, not this definition.

10. **NOTE — Four-attestation verification: numerical log claims confirmed; historical preservation and kernel-regression execution remain qualified.**

    **Files:** pack attestations 1–4; `audits/logs/emitter-spec-{sweep,axioms,lint}.log`; `scripts/ab_ch1_module_order.txt`; the four attached `Build/` sources.

    | Attestation | Result of this audit |
    |---|---|
    | 1. Commit `883ebc79`, 1,467 insertions, zero deletions, no pre-existing text changed | **Not independently verifiable from this bundle.** No parent snapshot, commit diff, or Git objects are attached. Current files cannot establish a historical no-deletion claim. No contradictory evidence found. Supply the pinned diff/baseline to verify it. |
    | 2. Fresh 57/57 sweep, no errors, 18 admissions | **Printed counts verified.** Exactly 57 distinct `CHECK` entries occur, in the exact order of the 57-line module list; zero `error:` lines; 18 admission warnings; final `FULL_SWEEP_COMPLETE`. The warnings split as 13 outside Build plus Wrappers 1, Loop 1, Primitives 3. Comment-stripped source inspection finds exactly the five named new `sorry` sites in Build. A fresh output directory and actual execution against these bytes cannot be independently established from the text log. |
    | 3. All epoch-2 expectations unchanged | **Reported outcome confirmed, independent closure verification unavailable.** The eight-line log states the closure pass and `lean exit: 0`; its two explicit root prints are `capture_run: []` and the expected self-root of `EXP_subset_NEXP`. It does not print the ten target inventories or include the closure program. Its provenance is `76b1aea001098e605d3391ff03346275f5652a35 + working-tree spec edits`, not the final spec-commit hash. This is consistent with a pre-commit run, but the checked-byte linkage and unchanged expectations remain maintainer attestations. |
    | 4. Lint and documentation | **Lint summary confirmed:** 0 FAIL / 2 WARN, both Loop/Primitives size warnings, plus Wrappers' informational size message. §11 records the in-file/D7 rationale. The “every new declaration” documentation clause needs the qualification in finding 5; the actual D7 decision record and lint program are not attached. |

    These limitations do not justify claiming a failed Lean sweep or a regression. They also do not justify describing all four attestations as independently verified. The gate remains open specifically on findings 1 and 2; findings 3–5 are separately actionable minor corrections.

Notation: `++` is list concatenation; `[]` is the empty list; `|x|` is list length. `P_p(c)` prefixes configuration `c`'s output by the word `p`; `a` is an action in the wrapper/step equations. `s_i` is the iterated loop state and `p_i` the concatenation before round `i`; `n=|x|`, `t` and `u` are elapsed times, and `L` is fuel-bit length. In budget formulas, `K` and `c` are fixed construction constants. In the exponential specialization only, `a` is the width coefficient, `d` the degree, and `B` the evaluator's time coefficient. `m` is a natural length, `r` a remainder word, and `true^m` a list of `m` true bits. Other identifiers are the supplied Lean declarations or their parameters.
