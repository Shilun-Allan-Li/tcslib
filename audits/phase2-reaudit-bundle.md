# External audit pack — Phase 2, round 2 (re-audit of fixes)

Round 1 (`audits/phase2-findings.md`, attached) audited the phase-2 skeleton at
`2917a1b9` and returned 4 majors, 6 minors, and 3 notes — none refuting a theorem
formula; all 11 new `sorry`s were assessed true as stated. All findings were accepted
and resolved at commit `85b66f2a`, **entirely at the prose/sketch/plan level: no Lean
statement changed**. This round verifies the fixes. Phase 2's gate closes when this
round returns no blockers or majors. Record findings in
`audits/phase2-reaudit-findings.md`.

## Resolution changelog (round-1 finding → change made)

| # | Finding (round 1) | Resolution |
|---|---|---|
| 1 | major — "frozen heads force length-determined halting" is false | Implication removed from `Oblivious.lean`'s design notes and the plan's decision log; both now cite the counterexample and state that `TimeConstructible` is needed by the construction, not forced by the definition; the possible future normal form (`M.k = 1 ∧ M.Oblivious`, length-determined halting) is flagged as separate conjuncts for the Cook-Levin work. |
| 2 | major — inadequate oblivious-simulation sketch | Sketch replaced by the round-1 construction: constant-input substitution for the constructibility witness, one fixed input-copy scan then parked real head, `B n = (a+1)·(T n +1)` fixed-sweep macrosteps over a marked layout with idling, fixed-duration block coding, fixed-time final emission; cost analysis `O(b·(T n +1) + (B n)²)`. |
| 3 | major — convention obligations wrongly recorded as discharged | Re-recorded as **waived** in the plan (per the fix option round 1 offered): no read-write-output model is formalized, so no bridge is statable; compensating restriction that no exact-step-count transfer from [AB09] is ever claimed; `Composition.lean`'s docstring rewritten to say exactly what it does and does not provide. |
| 4 | major — ModelInvariance overstates invariance | Module docstring now states delivered strength: alphabet-invariance of `DTIME` (constant absorbed), tape-count invariance of `P` only, explicitly disclaiming fixed-`DTIME T` tape invariance and citing [AB09, §1.6.1]'s matching scope. |
| 5 | minor — one-work-tape framing | "In-model analogue" framing adopted; the palindrome separation (linear here vs `Ω(n²)` merged, [AB09] chapter notes/Maass) added to the deviations as evidence the models differ; no identification claimed. |
| 6 | minor — obliviousness vs output schedule | Design note added: `Oblivious` constrains represented heads only; no output-head position exists; emission schedules unconstrained; bridge via fixed-time final emission noted. |
| 7 | minor — Exercise 1.5 coverage | Theorem relabeled as the exercise's *first assertion*, adapted; the two-tape normal form explicitly excluded; simultaneous normal form flagged for Ch. 2. |
| 8 | minor — blank block code | Sketch now encodes logical blank as the all-`none` block (lazily correct for never-visited blocks); no reserved binary code. |
| 9 | minor — marked-blank representation | Sketch now uses tagged `Option Γ` payloads + head flags + boundary tags; `k = 0` handled by an unused tape. |
| 10 | minor — folding coordinate | Sketch now uses `φ z = if 0 ≤ z then z else -z-1` (noting `φ 0 = φ (-1) = 0`), origin tags written at initialization, component flip without physical move at the fold, and safe-halt on non-embedded symbols for the universal `NonnegativeHeads` obligation. |
| 11-12 | notes | Documented (Claim 1.5's dropped time-constructibility hypothesis and string-output generalization; constant-absorption calculations retained for the fill phase). |
| 13 | note — stale scope paragraph | Plan §5 phase-2 paragraph aligned with the decision log (waiver + Ch. 3 deferral). |

## Brief for the auditor

Same ground rules as previous rounds (trusted surface only; no blanket approval).
This round's tasks, in priority order:

1. **Verify each changelog row** resolves its finding without introducing new defects.
   Since no Lean statement changed, the emphasis is on whether the corrected prose now
   matches the declarations and whether the corrected sketches are now adequate
   blueprints for the stated bounds.
2. **Re-read the two corrected load-bearing sketches** (`oblivious_of_mem_DTIME`,
   `nonnegative_heads`) as if refereeing a proof outline: identify any remaining gap
   that would surface only at formalization time.
3. **Assess the waiver text** (`Composition.lean` + plan) on its own terms: does the
   restriction "no exact-step-count transfer from [AB09] is ever claimed" actually
   hold across the current development's docstrings?
4. Spot-check that nothing else drifted (statements at `85b66f2a` are byte-identical
   to `2917a1b9` for all theorem formulas).

## Specific questions

1. In the corrected oblivious construction, step (1) substitutes constant input reads
   into the constructibility witness's table. Confirm this preserves the witness's
   *output* (it must still be `⌞T n⌟` — the budget depends only on `n`, but check the
   argument that the substituted machine computes the same value it computes on the
   all-`false` input, and that `ComputesInTime` on the all-`false` input is what the
   witness's specification provides).
2. Step (2) copies the input then parks the real head. Is one fixed scan sufficient
   given that the layout preparation in step (3) may need the input *length* encoded
   in unary or binary — and is that length information obtainable obliviously?
3. In the folding fix, origin tags are written "during a constant-cost
   initialization". Verify a machine can write a tag at cell 0 of each tape in O(1)
   steps *before* any simulated activity, and that the tag never collides with
   simulated payloads (does the alphabet need a dedicated origin component?).
4. The waiver's restriction claim (question 3 of the brief): scan the development's
   docstrings for any remaining sentence that transfers an exact [AB09] step count
   into a formal statement.
5. Any residual issue with the `mem_P_iff_one_work_tape` forward direction now that
   invariance claims were restated (the theorem itself was untouched)?

## Scope

| Item | Where |
|---|---|
| Files under audit | the six phase-2 files as amended (`Composition.lean`, `Robustness/*.lean`, `ModelInvariance.lean`), plus the amended plan decision log |
| Source text | Arora & Barak 2009, §1.3.1 (PDF pp. 42-45), §1.6.1 (PDF pp. 51-52), Exercise 1.5 (PDF p. 60) |
| Context | round-1 findings (attached), `AroraBarakChapter1Plan.md`, `policy.md` |
| Out of scope | tactic scripts; phase-1 surface (closed loop); theorem formulas confirmed in round 1 (spot-check only) |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.

---

# ATTACHMENT A — Round-1 findings (context for verifying resolutions)

**Phase 2 external audit: statements, model fidelity, and proof obligations**

Audited the supplied `phase2-bundle.md`, identified by its brief as commit `2917a1b9` on `complexity/arora-barak-ch1`, against the attached Arora–Barak textbook. The principal source locations are printed pp. 16–19 (PDF 42–45), pp. 25–26 (PDF 51–52), and Exercise 1.5 on p. 34 (PDF 60). I additionally checked the underlying tape model on pp. 12–13 and the intended Cook–Levin use on pp. 47–49 (PDF 73–75).

This is a mathematical statement/source audit, not a Lean proof certificate. The packet contains 11 new `sorry`s and 28 in total, as advertised. Lean and Lake are unavailable in this environment, so I have not independently reproduced the claimed successful elaboration or verified the repository commit. Phase-1 material was spot-checked only. The input attachments were not modified.

There are four major findings concerning a false implication, an inadequate simulation sketch, an undischarged model bridge, and an overstatement of time-class invariance. These findings do not establish a counterexample to any of the eleven new Lean theorem statements; the declaration-specific assessments below distinguish mathematical plausibility and constructive arguments from completed formal proofs.

The following restatements were made from the declaration bodies, extracted without Lean comments, before comparing their docstrings. File references abbreviate the attached paths: machine files live under `TCSlib/Complexity/TuringMachine/`, and class files under `TCSlib/Complexity/ClassP/`. The plan decision log refers to `AroraBarakChapter1Plan.md`.

| Declaration | Independent mathematical restatement | Comparison with the source |
|---|---|---|
| `TuringMachine/Finite.lean` · `ComputesFunInTimeVia` | On every string over the source alphabet, the machine halts by the stated length bound on the symbolwise embedded input and produces the symbolwise embedded function value. It imposes no computation requirement on other target-alphabet inputs. | Appropriate interface for binary inputs and outputs inside a larger common tape alphabet; more generally usable for an embedded source alphabet. This is not a promise restricted to some binary strings. |
| `Composition.lean` · `computesFunInTime_id` | Some finite binary machine copies every input within a constant times its length plus one. | Technical composition infrastructure consistent with §1.3; not a separately numbered AB claim. |
| `Composition.lean` · `computesFunInTime_const` | For each fixed binary word there is a finite binary machine producing it on every input within a constant times the input length plus one. The machine and constant may depend on the word. | Correct but weaker than the available constant-time bound in the input length. |
| `Composition.lean` · `computesFunInTime_comp` | Given total computations of two binary string functions with the stated budgets, and a nondecreasing second budget, a finite binary machine computes their composition within a constant times the sum of the first budget, the second budget evaluated at the first, and one. | A valid quantitative version of the high-level composition convention; it concerns this append-only model throughout. |
| `Robustness/AlphabetReduction.lean` · `alphabet_reduction` | A finite-alphabet machine computing a total binary string function through a bit embedding has a binary simulator with exactly the same number of work tapes and time at most a constant times the original budget plus one. | Acceptable in-model analogue of Claim 1.5. It generalizes Boolean output to strings and drops time constructibility; neither is needed by this simulation. The explicit logarithmic constant is not retained. |
| `Robustness/SingleTape.lean` · `one_work_tape` | A total string computation over any finite alphabet can be reproduced through an embedding into a finite enlarged alphabet using exactly one work tape in padded quadratic time. | A weaker target restriction than Claim 1.6: dedicated input and output remain. Accept the declared restricted scope, not equivalence to the merged single-tape claim. |
| `Robustness/SingleTape.lean` · `one_work_tape_binary` | A total binary string computation has a binary simulator using exactly one work tape with the same padded quadratic bound. | Correct combination of the preceding two in-model statements; it still does not merge input, work, and output. |
| `Robustness/Bidirectional.lean` · `NonnegativeHeads` | On every initialized input and at every time, each work head has a nonnegative integer coordinate. Nothing is required of arbitrary starting configurations. | Appropriate semantic predicate for unidirectional work-tape use in the existing model. |
| `Robustness/Bidirectional.lean` · `nonnegative_heads` | A total finite-alphabet computation has a finite enlarged-alphabet simulator preserving the work-tape count, computing the embedded function with constant slowdown, and using nonnegative work coordinates on every input over its enlarged alphabet. | Acceptable in-model analogue of Claim 1.8. The nonnegativity obligation includes inputs outside the embedding range, although functional correctness does not. |
| `Robustness/Oblivious.lean` · `Oblivious` | At each natural-number time, every two inputs of equal length give the same numerical input-head position and the same tuple of work-head positions. It says nothing about states, halting indicators, or output emissions. | Matches length-dependent trajectories of the heads represented in this model. It does not imply equal halting times and is not, without a bridge, AB's predicate on all physical heads. |
| `Robustness/Oblivious.lean` · `oblivious_of_mem_DTIME` | A language in `DTIME T`, for time-constructible `T` in the repaired sense, has some finite binary decider satisfying that head-position predicate within padded quadratic time. | The literal formula is supportable. It contains neither the two-tape normal form from Exercise 1.5's final sentence nor a uniform-halting conclusion. |
| `ClassP/ModelInvariance.lean` · `DecidesInTimeVia` | On every embedded binary input, the machine halts within the stated bound and outputs exactly the embedded membership bit. | Correct embedded-alphabet form of a decider from §1.6. |
| `ClassP/ModelInvariance.lean` · `mem_DTIME_of_decidesInTimeVia` | Such a finite-alphabet decider puts the language in binary `DTIME` for the original budget plus one, with a constant absorbed into the class definition. | Valid alphabet-invariance direction; no tape-count invariance of a fixed time class is asserted by this theorem. |
| `ClassP/ModelInvariance.lean` · `mem_P_of_decidesInTimeVia_poly` | An embedded finite-alphabet decider with any stated polynomial bound puts the binary language in `P`. | Valid alphabet-invariance corollary of §1.6.1 within the declared conventions. |
| `ClassP/ModelInvariance.lean` · `mem_P_iff_one_work_tape` | A language is in `P` exactly when some binary machine with one work tape decides it within a constant times a power of input length plus one. | Correct invariance of `P` under reducing the number of work tapes to one; not a bridge to AB's merged single-tape structure. |

The findings table uses the severity definitions in the brief.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `Robustness/Oblivious.lean` · `Oblivious` design; plan decision log | Frozen heads force length-determined halting. | A two-live-state machine with no work tapes keeps its input head stationary, halts after one step on `[false]`, and after two on `[true]`. It satisfies `Oblivious` on all inputs. The complete transition table and induction appear below. | Remove the implication from both documents. If a downstream normal form needs equal halting times, prove it separately or add it to that normal-form theorem. |
| 2 | major | `Robustness/Oblivious.lean` · `oblivious_of_mem_DTIME` | The supplied sketch establishes the quadratic oblivious simulation. | `one_work_tape_binary` already has a quadratic time bound; only linearly many simulated steps of its output are not justified. The time-constructibility witness can have input-dependent trajectories, and retaining a simulated machine's real input-head moves also fails obliviousness. | Run the clock on a virtual constant string of the same length; copy the real input; sweep a fixed layout of the original machine for a length-determined budget, including its virtual input head. Use fixed-duration binary coding. This supports the literal theorem without strengthening `TimeConstructible`. |
| 3 | major | `Composition.lean` · module design; plan decision log | Composition discharges the read-write/append-only output and initialization convention obligations. | Both hypotheses and the conclusion of `computesFunInTime_comp` already use append-only output. Its intermediate buffer receives irrevocable emissions; no read-write-output source model, final-output extraction, or initialization relation appears in the statement. Existential constants do not establish semantic equivalence. | Add explicit simulation statements and configuration invariants before recording these obligations as discharged, or mark the bridges deferred/waived and restrict source-transfer claims accordingly. A new proof need not precede the skeleton, but the missing bridge statement must. |
| 4 | major | `ClassP/ModelInvariance.lean` · module description | `DTIME` up to constants and `P` are independent of alphabet size and number of work tapes. | Constant slowdown is supplied for alphabet reduction; tape reduction supplies a quadratic bound. The theorems do not justify preserving a fixed `DTIME T` when reducing tapes. AB §1.6.1 draws polynomial-time invariance, not invariance of every time class. | State separately: alphabet reduction preserves time up to a constant; tape reduction preserves polynomial time with quadratic overhead. Keep the existing theorem formulas. |
| 5 | minor | `Robustness/SingleTape.lean` · `one_work_tape`, `one_work_tape_binary`; `mem_P_iff_one_work_tape` | One work tape is a faithful replacement for all of Claim 1.6. | AB explicitly merges input, work, and output. The retained input/work pair can decide palindromes in linear time; the book records a quadratic lower bound for the merged single-tape model. This difference survives constant absorption. | Call these “in-model analogues” and retain the declared exclusion of the merged model. Do not mark the full cross-model claim proved. The restricted scope itself is acceptable. |
| 6 | minor | `Robustness/Oblivious.lean` · `Oblivious`; brief rendering 4 | Omitting output positions literally matches AB's all-head definition. | AB's output tape is a read-write tape with a head; the present stream has no such position field. Equality of the two stored kinds of head positions places no restriction on output emission schedules. Conversely, AB head-position equality does not by itself require equal write times. | Explicitly identify this as input/work-head obliviousness under the stream-output convention. For a direct all-head bridge, specify how output is represented; a fixed-time final emission works for the current one-bit decider theorem. Do not silently identify AB write times with stream length. |
| 7 | minor | `Robustness/Oblivious.lean` · `oblivious_of_mem_DTIME` | The statement covers the whole normal-form conclusion of Exercise 1.5. | The exercise additionally requires one input tape and one work/output tape. The theorem leaves `M.k` unrestricted. A separate existential one-work-tape theorem cannot be conjoined with this existential oblivious theorem without a preservation argument. | Label the theorem as the first assertion, adapted to this model. If the later proof needs both properties, add a simultaneous normal form, at least `M.k = 1 ∧ M.Oblivious`, with its output-convention bridge. |
| 8 | minor | `Robustness/AlphabetReduction.lean` · `alphabet_reduction` sketch | The stated binary block length can encode every nonblank symbol and reserve an additional binary code for blank. | For two nonblank symbols the proposed length is one, leaving only two binary codes for three logical values. The physical alphabet also contains `none`, but the sketch does not distinguish that solution from reserving a binary code. | Encode logical blank by an all-`none` block and nonblank symbols by binary blocks; explain lazy initialization. Alternatively enlarge the binary block length and give an explicit representation of initially blank blocks. No extra work tape is necessary. |
| 9 | minor | `Robustness/SingleTape.lean` · `one_work_tape` sketch | Pairs of a source symbol and a head flag suffice for the stated marked-cell representation. | Source cells have type `Option Γ`, and every initial scanned cell is blank. The literal product `Γ × Bool` omits a marked blank; it also needs a specified treatment of sweep boundaries. | Use tagged `Option Γ` payloads, head flags, and boundary information in the enlarged finite alphabet. Handle `k = 0` separately by adding an unused tape. |
| 10 | minor | `Robustness/Bidirectional.lean` · `nonnegative_heads` sketch | The origin is directly detectable and folded coordinates are absolute values. | The transition table cannot read a head coordinate, and all work tapes start blank. With pairs `(j, -j-1)`, the virtual positions `0` and `-1` both map to physical fold coordinate zero; this is not absolute value. | Initialize an origin tag or sentinel and preserve it. Use the piecewise folding coordinate described below, with any sentinel offset stated explicitly, and specify safe handling of non-embedded input symbols. The theorem's formula need not change. |
| 11 | note | `Finite.lean` · `ComputesFunInTimeVia`; `AlphabetReduction.lean` · `alphabet_reduction` | All binary inputs, an arbitrary bit embedding, and the unchanged tape count are appropriate. | The alphabet may contain irrelevant other input symbols. On a valid input every emitted symbol belongs to the final embedded output because output only grows; even an early emission cannot later be erased. Finite control and fixed blocks suffice with the existing tapes. | No statement change. Document the generalization from Boolean to string output and the unnecessary time-constructibility hypothesis from the original claim. |
| 12 | note | `Composition.lean` · `computesFunInTime_comp`; `SingleTape.lean` · binary corollary; model-invariance corollaries | The length substitution and constant-absorption inequalities are valid. | Intermediate output length is at most actual halting time and hence the first budget. Monotonicity gives the required second-budget comparison. The padded square is at least one, so the extra alphabet-reduction constant is absorbable at every input length. Calculations are below. | Keep the statements. Global monotonicity is sufficient; eventual monotonicity or a finite maximum would support optional alternative APIs. |
| 13 | note | Plan decision log; `Oracle.lean` · convention disposition | Defer persistent-versus-erased query-tape polynomial simulation to the oracle-class phase. | None of the new results depends on this bridge, and no oracle complexity class is defined here. The current documentation already forbids transporting exact time bounds across these conventions. | Accept the deferral, with an explicit outstanding obligation before importing oracle-class invariance. Update the older phase-2 scope paragraph to agree with the decision log. |

The following arguments assess each of the eleven new `sorry`s as literally stated. They are constructive mathematical assessments, not claims that the unimplemented transition invariants have already been formalized.

| New `sorry` | Literal-statement assessment, with a 2–5 sentence argument |
|---|---|
| `computesFunInTime_id` | A machine with no work tapes emits the current input bit and moves right on each bit, then halts when it reads the right blank. It takes exactly `n + 1` steps, including one step on empty input, so constant one witnesses the theorem. One live state suffices because `none` is the halting state. |
| `computesFunInTime_const` | Use one live state for each successive output position and a final live state that halts on its next transition. This emits the fixed word and halts within its length plus one, independently of the input. Taking the theorem's constant to be that positive number gives the required bound even at length zero. |
| `computesFunInTime_comp` | Simulate the first machine while diverting its output to one fresh work tape, using fixed binary blocks for data and distinguishable boundaries. Rewind this buffer and simulate the second machine with its bounded input head represented on the buffer; the other two groups of work tapes simulate the original work tapes. The buffer length and rewind cost are at most a constant times the first budget, and monotonicity bounds the second phase by the second budget evaluated at the first. Phase switching and empty-buffer handling have constant cost, giving the stated sum. |
| `alphabet_reduction` | Store each original work cell in a fixed-length block on the corresponding binary work tape, with an all-blank block representing logical blank and binary blocks representing nonblank symbols. Finite control holds the original state, scanned symbols, and block phase, while actual input bits are interpreted through the embedding. On every valid input the output-prefix property ensures every emission has a bit preimage, so a finite decoder preserves output. A fixed number of microsteps per original step and constant startup give the bound while preserving the work-tape count, including zero. |
| `one_work_tape` | For positive tape count, interleave cells on one tape and explicitly encode marked blanks and sweep boundaries. After a given number of original steps, each head lies within that distance of its origin, so the interleaved active interval has length linear in that number, with a machine-dependent constant. A constant number of sweeps and bounded local mark updates simulate each step, and summing their costs gives the padded quadratic bound. For zero original work tapes, add one unused tape. |
| `one_work_tape_binary` | Apply the previous theorem and then alphabet reduction through its returned embedding. Alphabet reduction preserves the already established one-work-tape count. Its additive constant is bounded by a multiple of the padded square using the calculation below. |
| `nonnegative_heads` | Fold each work tape, retain a component bit for each virtual head, and initialize a detectable origin tag or sentinel. Crossing between virtual cells zero and minus one changes the component without moving the fold coordinate below zero; other moves change that coordinate by at most one. Source symbols outside the chosen input embedding can cause a safe halt, so nonnegative use holds even on malformed enlarged-alphabet inputs. Initialization and each simulated step cost a fixed constant, preserving the original work-tape count. |
| `oblivious_of_mem_DTIME` | The literal theorem is supportable, but its supplied sketch is inadequate for finding 2's reasons. Run the constructibility witness with every nonblank input symbol replaced by a fixed bit; its complete run then depends only on length and still computes the required budget. Copy the real input and simulate the original decider directly by fixed sweeps over a budget-sized marked layout, keeping the real input head parked during that simulation. Pad simulated halting, use a length-dependent counter and fixed-duration binary coding, and emit the stored answer at the end. This gives quadratically bounded trajectories and termination determined by length; the more explicit construction obligations are recorded below. |
| `mem_DTIME_of_decidesInTimeVia` | Apply alphabet reduction to the string function returning the singleton membership bit. Its result is a binary decider with budget a constant times the original budget plus one. That constant is precisely the witness required by the definition of the concluding `DTIME` class. |
| `mem_P_of_decidesInTimeVia_poly` | The preceding theorem yields `DTIME` membership for the given polynomial plus one. For every length, this is dominated by `(C + 1) * 2^d * (n^d + 1)`, as calculated below. Absorb constants and use the corresponding component of `P`. |
| `mem_P_iff_one_work_tape` | Forward, the existing polynomial characterization supplies a binary decider, to which the one-work-tape binary theorem applies. The resulting squared polynomial is bounded by `c * (C + 1)^2 * (n + 1)^(2*d)` at every length. Reverse, forget the tape-count conjunct and apply `mem_P_iff`. |

Here is a fully specified counterexample to the false implication in finding 1. Use zero work tapes, live states `start` and `delay`, and initial state `start`. Every action has zero input-head movement; the tuple of work actions is the unique empty tuple.

| Current state | Read input symbol | Emission | Successor state |
|---|---|---|---|
| `start` | `some true` | none | `some delay` |
| `start` | `some false` or `none` | `false` | `none` |
| `delay` | any | `true` | `none` |

This specifies a finite `FinTM Bool` transition table on every possible read. From `Cfg.init`, the numerical input-head position is one; `moveInputPos_zero` and induction on the number of steps imply that it is one at every time on every input. The work-position tuple is unique because the work-tape index type is empty. Therefore the two equalities in `Oblivious` hold for every pair of equal-length inputs and every time, including after halting.

On input `[false]`, the state is `some start` at time zero and `none` at time one. On input `[true]`, it is `some start` at time zero, `some delay` at time one, and `none` at time two. Thus the first halting times are respectively one and two although both inputs have length one. This also gives a total decider with input-dependent halting time; nontermination is not needed for the counterexample.

The definition already compares input-head positions after both halts: its quantifier ranges over all natural-number times. Adding that same comparison again cannot repair the implication. AB's Cook–Levin discussion on printed p. 47 explicitly assumes both equal runtime and prescribed head positions; to follow that normal form literally, add a separate guarantee of length-determined halting. Alternatively, a bounded tableau can run every computation to a common length-dependent upper bound using the existing absorbing halted configurations; this route needs no theorem that `Oblivious` alone determines the first halting time.

Output timing is a separate issue. A finite machine can keep all represented heads stationary, halt on every input after two steps, and emit its single answer on step one for a first bit `false` but on step two for a first bit `true`; therefore even equal first halting times would not constrain emission times. If one defines an implicit stream-output position as the number of emitted symbols, this example violates its obliviousness. AB's read-write output head, however, can write without moving, so equality of such stream positions is a choice of bridge, not a literal consequence of AB's wording. For decision computations, buffering the answer in finite control and emitting once at a common final time resolves this issue.

The main quantitative checks are as follows; they also address sublinear bounds and small inputs without importing AB's exact step counts.

1. **Composition and early emissions.** Let the actual first halting time of the first machine on `x` be `τ`. Absorption and `output_length_le` give

   \[
   |f(x)|
   =|\operatorname{output}(\operatorname{run}(x,\tau))|
   \le \tau\le T_1(|x|),
   \qquad
   T_2(|f(x)|)\le T_2(T_1(|x|)).
   \]

   Simulate, rewind, and switch phases in at most

   \[
   c_0\bigl(T_1(|x|)+|f(x)|+T_2(|f(x)|)+1\bigr)
   \le 2c_0\bigl(T_1(|x|)+T_2(T_1(|x|))+1\bigr),
   \]

   where `c₀` bounds the fixed per-step and phase-switching overheads; take `c = 2*c₀`. The proof uses no monotonicity of the first budget. Eventual monotonicity of the second budget would also suffice after absorbing the finite exceptional maximum; without either condition, replacing the evaluated second budget by the maximum over lengths up to the first budget is a valid alternative.

   On an embedded input, every output prefix up to the budget is a prefix of `(f x).map e`; hence every emitted symbol belongs to the range of the embedding. Past that budget, the machine is halted and emits nothing. An emission before the rest of the input has been read does not escape this argument: the total-computation hypothesis already requires that irrevocable emission to be correct.

2. **Visited-zone growth.** At original step `t`, every work-head coordinate lies between `-t` and `t`, by induction from zero using the one-cell movement bound. For positive `k`, the coordinates `j*k+i`, with `0 ≤ i < k`, fit in an interval of `k*(2*t+1)` cells; fixed guard blocks and boundary tags add at most a constant multiple of `k + 1`. For a run halting at `τ ≤ T(n)`, a constant-per-cell sweep construction therefore costs at most

   \[
   c_0+c_0\sum_{t=0}^{\tau-1}(t+1)
   =c_0\left(1+\frac{\tau(\tau+1)}2\right)
   \le 2c_0(T(n)+1)^2.
   \]

   Here `c₀` is a fixed overhead bound for this construction. No scan of the whole input is required for this in-model work-tape reduction, so no hypothesis `T(n) ≥ n` or time constructibility is needed here. This observation does not supply a bridge to the merged tape model.

3. **Binary-corollary constant.** Since `(T(n)+1)^2 ≥ 1`,

   \[
   c_2\bigl(c_1(T(n)+1)^2+1\bigr)
   \le c_2(c_1+1)(T(n)+1)^2.
   \]

   Thus `c = c₂*(c₁+1)` works at all lengths, not just eventually.

4. **Polynomial corollaries.** For natural `n,d`, splitting off `n = 0` and using `n+1 ≤ 2n` for `n ≥ 1` yields

   \[
   (n+1)^d\le 2^d(n^d+1),
   \]

   including `d = 0`. Consequently,

   \[
   C(n+1)^d+1
   \le(C+1)(n+1)^d
   \le(C+1)2^d(n^d+1),
   \]

   and

   \[
   c\bigl(C(n+1)^d+1\bigr)^2
   \le c(C+1)^2(n+1)^{2d}.
   \]

   Moreover, any `DecidesInTimeVia` hypothesis on all binary strings implies `T(n) ≥ 1` at every length: instantiate it on a string of `n` false bits and use impossibility of zero-step halting. Thus the alphabet-invariance conclusion can even be strengthened from `DTIME (T+1)` to `DTIME T`, since `T(n)+1 ≤ 2T(n)`. This observation does not apply to tape reduction's squared bound.

5. **Folding.** The fold coordinate for the paired layout in the sketch is

   \[
   \phi(z)=
   \begin{cases}
   z,&z\ge0,\\
   -z-1,&z<0.
   \end{cases}
   \]

   It is always nonnegative, and `φ(0)=φ(-1)=0`. Crossing between these two virtual cells changes only the component flag; it must not issue an actual left move from physical zero. An origin tag can detect this case, or a sentinel can implement it with a stated positive offset and constant extra moves. Arbitrary configurations need not satisfy the invariant: a predicate requiring nonnegative coordinates from every possible starting configuration would already fail at time zero for any machine with a work tape.

For the oblivious theorem, the following replacement strategy explains why the repaired time-constructibility hypothesis suffices. These are the machine-construction obligations still requiring formal implementation; the paragraph is not presented as a completed Lean proof.

- Choose the decider constant `a` from `DTIME T`, and a constructibility machine with bound `b*(T(n)+1)`. Simulate the latter with every nonblank input symbol replaced in the transition table by `false`, while preserving the boundary blanks. Its behavior on any input of length `n` is exactly its behavior on the all-false input of length `n`, so all its states, trajectories, emissions, and termination time depend only on `n`. Redirect its budget output to a work tape.
- Copy the real input in a fixed scan and rewind as needed. This costs a constant times `n+1`, which is absorbed because `n ≤ T(n)`. All physical motions of this phase depend only on length.
- Set the number of simulated original steps to `B(n)=(a+1)*(T(n)+1)`. It bounds both `a*T(n)` and `n+1`. Prepare a layout of length at most a fixed multiple of `B(n)` containing the original work tapes, a virtual copy of the input, all virtual head markers, and counter information. Preparing counters and the layout can be done within the quadratic allowance by length-dependent operations.
- Simulate **one step of the original decider** by a fixed number of complete sweeps, each of length at most a fixed multiple of `B(n)`. The virtual input head is included in the layout, and the real input head stays parked. Data may affect writes, simulated states, and virtual markers, but never the physical sweep path or its duration; after simulated halting, continue the same schedule idly. Fixed-duration block coding gives a binary machine without relying on the bare existential alphabet-reduction theorem to preserve obliviousness.
- Perform exactly `B(n)` such macrosteps and emit the stored one-bit answer at the end. Counter maintenance can be charged within the per-macrostep linear allowance. The total cost is at most a machine-dependent constant times `b*(T(n)+1)+B(n)^2`, hence at most a constant times `(T(n)+1)^2`; the full physical schedule and actual first halting time depend only on length.

An arbitrary constructibility witness cannot simply be assumed oblivious: add one scratch tape, move its head left or right depending on the first input bit, restore it, and then run any valid witness. The resulting witness still has cost at most `(b+2)*(T(n)+1)` and the same output, but has different trajectories at the first step. The constant-input substitution above removes that dependence without presupposing an oblivious-simulation theorem. Likewise, `one_work_tape_binary` is not a black-box linear-time preprocessing step: it supplies a quadratic bound, and applying another generic quadratic simulation to that bound would yield a fourth power. The direct sweep construction avoids that unjustified composition.

There is no loss of binary inputs from allowing an arbitrary bit embedding. When translating a particular AB machine, choose the embedding to name its designated data bits; a different embedding simply describes a different symbol encoding, and the input interpretation and output decoding use it consistently. Strings containing other alphabet symbols are not in the binary function's domain. Quantifying over every binary string is essential for the advertised language-class corollaries, which are not promise-problem claims.

The following adversarial instantiations were attempted. Outcomes follow from the definitions; finite executable spot-checks of the stationary-head example and the constant inequality were supplemental checks only, not substitutes for the arguments above.

| Case | Instantiation | Outcome |
|---|---|---|
| A1 | `T = fun _ => 0` in alphabet reduction, both one-work-tape results, and folding | Every computation premise fails already on the empty input, since an initialized machine has a live state. The padded conclusions do not make any premise satisfiable; these instances are vacuous. |
| A2 | `T = fun _ => 0` in oblivious simulation | Constructibility fails at length one because it requires `1 ≤ T(1)`, and `DTIME 0` is empty. No degenerate decider results. |
| A3 | `k = 0` in one-work-tape reduction and folding | Add an unused tape for the first theorem. In folding, retain zero work tapes: the nonnegativity quantifier is empty, and the original machine with identity embedding already supplies a witness after weakening the budget. |
| A4 | A one-element alphabet in alphabet reduction | No injection of the two Boolean values exists. This is appropriate: the interface requires two distinct represented data symbols; the separate blank is not a third input data symbol. |
| A5 | Two nonblank symbols in the alphabet-reduction sketch | A one-bit binary code cannot also reserve a binary blank code. All-physical-blank blocks supply the needed third logical value without an extra tape; this exposes finding 8 rather than refuting the theorem. |
| A6 | Identity as the first function, any fixed constant word as the second | With first budget `n+1` and second budget the word length plus one, the second budget is monotone and the composition bound dominates a direct constant-output machine, including on empty input. |
| A7 | A nonhalting machine with all heads stationary | It satisfies `Oblivious`, as a head-trajectory predicate should allow. It cannot witness the theorem's additional `DecidesInTime` conclusion. |
| A8 | A total stationary-head decider halting in one or two steps on equal-length inputs | This is the fully specified counterexample above. It refutes length-determined halting even with total correctness. |
| A9 | A fixed two-step halting time but different one-bit emission times | The represented heads can stay fixed while one branch emits on the first step and the other on the second. This isolates the output-schedule omission from the halting-time issue. |
| A10 | Virtual work-head path `0, -1, -2, -1, 0` | The corresponding fold coordinates are `0, 0, 1, 0, 0`. Component flips at the origin suffice; an actual move to physical minus one would violate the intended simulator invariant. |
| A11 | A first-step emission outside the bit embedding's range | No such run can satisfy the total embedded-output hypothesis on that input: the symbol remains in every later output prefix. Early emission does not break the decoding argument. |
| A12 | A constructibility witness with a first-bit-dependent scratch-head detour | The repaired budget still holds after increasing its constant, but the witness is not oblivious. Hence simply “running the witness” is not a correct first phase without the constant-input substitution or an equivalent argument. |
| A13 | The time bound `T(n)=n` in the oblivious theorem | The repaired constructibility predicate admits this bound, but the already adopted `DTIME` definition is empty at a bound vanishing on length zero. Thus this theorem instance is vacuous; a bound such as `n+1` is the applicable normalized example. This is a phase-1 convention, not a newly discovered contradiction. |
| A14 | Enlarged-alphabet inputs outside the folding embedding | Functional correctness is unrestricted there, but `NonnegativeHeads` still applies. Safe halting on any encountered invalid input symbol, with the same initialized fold invariant beforehand, satisfies the stronger universal head condition. |

The declared renderings therefore receive distinct dispositions: accept the embedded-alphabet formulation and same-tape alphabet reduction; accept one work tape as a narrower in-model analogue while rejecting identification with the merged model; accept initialized-run nonnegative work heads as the relevant in-model direction of folding; retain the represented-head obliviousness predicate but reject its claimed halting implication and qualify its output convention. The read-write-output and initialization obligations remain open, while deferring the oracle-tape polynomial bridge is acceptable for the present phase. The class-level corollaries establish the particular alphabet and one-work-tape conclusions stated, not unrestricted equivalence of all the source's models.

Notation used in this audit: `n` is input length; `t` is a step number; `τ` is an actual first halting time; `x` is an input string; `f,g` are string functions; `T,T₁,T₂` are natural-valued budgets; `e` is a symbol embedding; `Γ` is an alphabet of nonblank symbols; `k` is the number of work tapes; `j,z` are integer cell coordinates and `i` a tape index; `φ` is the displayed folding map; `B(n)` is the padded number of original steps in the replacement oblivious construction; `a,b` are its decider and constructibility constants; `c,c₀,c₁,c₂,C` are the locally specified constant factors; `d` is a polynomial degree; `|x|` denotes string length; and the displayed run/output operators are the given initialized-run and output operations. State names `start` and `delay` refer only to the counterexample. Big-O bounds hide constants depending on the fixed machines and alphabets, not on the input.

---

# ATTACHMENT B — Context documents

## ===== AroraBarakChapter1Plan.md =====

# Formalization Plan: Arora-Barak Chapter 1

**Branch:** `complexity/arora-barak-ch1` · **Governing standards:** [`policy.md`](policy.md)

This document is the working plan for formalizing Chapter 1 of Arora & Barak,
*Computational Complexity: A Modern Approach* (CUP 2009) — "The computational model — and
why it doesn't matter" (book pages 9–37) — in TCSlib. It records the foundation decision,
the architecture that keeps the model robust to variations (oracles, nondeterminism), the
module layout, and the phasing. Source tag throughout the development: `[AB09]`.

## 1. Scope: what Chapter 1 contains

| Section | Content | In scope |
|---|---|---|
| §1.2 | k-tape TM `(Γ, Q, δ)`: read-only input tape, work tapes, output tape (read-write in [AB09]; append-only write-only in our model — a variation [AB09, p. 19] itself sanctions, declared in `DTIME.lean`); start configuration; halting; Example 1.1 (palindromes in 3n steps) | Yes |
| §1.3 | Computing `f` in time `T(n)` (Def 1.3); time-constructibility; Claim 1.5 (alphabet reduction, `4 log|Γ|` slowdown); Claim 1.6 (k tapes → 1 tape, `5kT²`); Remark 1.7 (oblivious TMs); Claim 1.8 (bidirectional → unidirectional, `4T`) | Yes (oblivious: statement only at first) |
| §1.4 | Machines as strings: every string decodes to some TM, every TM has infinitely many encodings; universal TM; Theorem 1.9 (universal simulation), relaxed `O(T²)` version; time-bounded universal TM | Yes |
| §1.5 | Uncomputability: `UC` via diagonalization (Thm 1.10); `HALT` via reduction (Thm 1.11); §1.5.2 Gödel discussion | Thms 1.10–1.11 yes; Gödel material is prose — out of scope |
| §1.6 | `DTIME(T(n))` (Def 1.12, with constant absorption), `P` (Def 1.13), examples | Yes |
| §1.7 | Hennie-Stearns `O(T log T)` universal simulation (amortized zone argument) | Stretch goal, off the critical path |

Additionally in scope, ahead of the book's own ordering: the **oracle TM** definition
(the book defers it to §3.4). We pull it forward to validate that the architecture supports
model variations before the expensive theorems are built on it.

## 2. Foundation decision

**Decision: vendor cslib's multi-tape TM model; do not build on Mathlib's TMs; do not take
cslib as a dependency.** Findings behind this (surveyed Sept 2026, against our pinned
mathlib `029db123ddaa`, toolchain v4.25.0):

- **Mathlib** is a computability library, not a complexity library. It has no multi-tape TM
  (TM0/TM1 are single-tape, TM2 is a stack machine); its model-simulation theorems carry no
  time bounds; `TM2ComputableInPolyTime` is a stub whose only instance is `id`. Building
  Arora-Barak on it means fighting the design. What we do reuse: `Language`,
  `Turing.FinEncoding`, and (later, as an optional bridge) the recursion-theory stack
  (`Nat.Partrec`, `Halting`/Rice, `Reduce`, `RecursiveIn`).
- **cslib** (github.com/leanprover/cslib, `Cslib/Computability/Machines/Turing/MultiTape/`,
  Apache-2.0) has an Arora-Barak-style `MultiTapeTM` (its write-only output tape is an
  [AB09, p. 19]-sanctioned variation of the book's read-write one): read-only input
  tape, k work tapes, explicit time and space semantics, a nondeterministic
  variant, and configuration-count bounds — actively developed, with a complexity roadmap
  (issue #611) that plans oracles as a wrapper over any model.
- **Why vendor rather than depend:** cslib targets Lean v4.35.0-rc1 with the new module
  system; TCSlib is pinned to v4.25.0 and the PFR dependency chains us there. The vendored
  surface is small (~1,400 lines). We stay structurally aligned with upstream so we can
  migrate to a real dependency at the next toolchain bump, and upstream anything we prove
  that they lack (universal TM, robustness claims).
- Vendored files follow `policy.md` §2: original copyright headers preserved, source commit
  recorded, local modifications listed (expected: de-module-system syntax, import-path
  ports to v4.25 mathlib).

Reference mechanization to mine for proof architecture: the Isabelle AFP entry
`Cook_Levin` (Balbach) — the only completed Arora-Barak-faithful development. Its lemma
decomposition, especially for TM composition and the universal machine, transfers.

## 3. Architecture

### 3.1 The Action/apply split (model variations)

cslib's configuration layer mentions no machine: a step is an **`Action`** (input-head
move, per-work-tape write/move, optional output symbol, successor state) plus
**`Action.apply`** (its effect on a configuration). A *machine* is then just the thing
that **chooses** the action from the current state and read symbols. Every model twist is a
different chooser over the same configurations, the same `apply`, and the same run/time/
space measures:

| Model | Chooser |
|---|---|
| Deterministic TM (Ch. 1) | function `State × reads → Action` |
| Nondeterministic TM (Ch. 2) | relation over actions |
| Oracle TM (§3.4, Definition 3.4, pulled forward) | function consulting `O : Language _` via query tape and `q_query`/`q_yes`/`q_no` states (pairwise distinct: `OracleTM.WellFormed`) |
| Probabilistic TM (Ch. 7, future) | two transition functions + coin |

Because `DTIME`-style definitions are stated over the shared run layer, `P`, `Pᴼ`, and
later `NP`/`BPP` are instances of one pattern, not parallel developments. Phase 1 locks
the design with sanity theorems in both directions: a plain machine embeds as an oracle
machine whose runs are in lockstep with the original under *every* oracle
(`ofMultiTapeTM`), and conversely an oracle machine run with the empty oracle is
eliminated into a plain machine in exact lockstep (`plainEmptyOracle`).

### 3.2 Finiteness: raw layer vs. bundled layer

Finiteness of `Γ` and `Q` is mathematically non-negotiable: with infinite states, δ can
memorize the input and decide any language in linear time (P would collapse to all
languages), and `⌞M⌟` has no finite representation. The design question is only *where*
the hypothesis lives:

- **Raw layer** (`MultiTapeTM k Γ Q`, parametric types, no finiteness): configurations,
  `step`, runs, time/space counting, and simulation *constructions*. Deferring finiteness
  here keeps semantics lemmas clean and lets compound state types (`Q × Γᵏ`, `Option Q`,
  sums) arise without instance-threading; finiteness of a constructed machine is an
  afterthought (`inferInstance`). This follows both cslib and mathlib TM0/TM1 practice.
- **Bundled layer** (`FinTM Symbol`: a raw machine bundled with `Fintype`/`DecidableEq`
  instances for its *state* type — analogous to mathlib's `FinTM2`): **all headline
  definitions and theorems** — `DTIME`, `P`, `⌞M⌟`, Theorem 1.9, oracle classes — are
  stated exclusively over the bundled layer, so a finiteness hypothesis can never be
  forgotten. The alphabet is *not* bundled: it stays an explicit parameter, fixed to
  `Bool` by the headline classes; results over a general `Symbol` (e.g. machine
  encodings) take `[Fintype Symbol]`/`[DecidableEq Symbol]` at their statements, and
  oracle complexity classes (Ch. 3) will introduce a finite oracle-machine bundle
  before they are defined. Encoding needs `Fintype`/`DecidableEq` as *data* (δ's table
  must be enumerated), which is why the bundle carries instances rather than `Finite`
  propositions.

Per `policy.md` §1 (layering), the raw layer is internal plumbing; the bundled layer is
the textbook object.

### 3.3 Conventions

- **Strings/languages:** `{0,1}*` as in the book; languages via mathlib's `Language`.
- **Namespaces:** `Turing` for the vendored core (minimizes diff against upstream; no
  clashes with mathlib's `Turing.*` at our pin), `Complexity` for classes and
  uncomputability. Revisit only if a clash appears.
- **NP/NTM:** strictly Chapter 1 here. cslib's nondeterministic file is in the vendorable
  set but lands with the Chapter 2 effort.

## 4. Module layout

Per `policy.md` §1: facades, 150–600-line files, precise imports, `TCSlib.lean` exports.

```
TCSlib/Complexity/TuringMachine.lean          -- facade + module docstring
TCSlib/Complexity/TuringMachine/
  Configuration.lean      -- Cfg, Action, Action.apply, space measure   [vendored]
  Deterministic.lean      -- MultiTapeTM, run, ComputesInTime(AndSpace) [vendored]
  Finite.lean             -- bundled FinTM layer (§3.2)
  Oracle.lean             -- oracle wrapper over the same Cfg/Action layer
  Composition.lean        -- sequential composition, basic combinators
  Robustness/
    AlphabetReduction.lean  -- [AB09, Claim 1.5]
    SingleTape.lean         -- [AB09, Claim 1.6]
    Bidirectional.lean      -- [AB09, Claim 1.8]
    Oblivious.lean          -- [AB09, Remark 1.7] (statement; proof deferred)
  Encoding.lean           -- ⌞M⌟ : TM ↔ string; totality + padding [AB09, §1.4]
  Universal.lean          -- [AB09, Thm 1.9] relaxed O(T²) + timed variant
  UniversalEfficient.lean -- [AB09, §1.7] Hennie-Stearns O(T log T)  [stretch]
TCSlib/Complexity/Uncomputability.lean        -- facade
TCSlib/Complexity/Uncomputability/
  Diagonalization.lean    -- UC, [AB09, Thm 1.10]
  Halting.lean            -- HALT, [AB09, Thm 1.11]
  MathlibBridge.lean      -- link to Nat.Partrec / Rice  [optional, later]
TCSlib/Complexity/ClassP.lean                 -- facade
TCSlib/Complexity/ClassP/
  DTIME.lean              -- decides, DTIME with constant absorption [AB09, Def 1.12]
  TimeConstructible.lean  -- time-constructibility [AB09, §1.3]
  P.lean                  -- P, closure basics, model-invariance [AB09, Def 1.13]
  Examples.lean           -- PAL ∈ DTIME(n+1) [AB09, Ex 1.1]; selected Ex 1.14
```

## 5. Phasing

Each phase lands first as a **compiling sorry-skeleton** (the GraphTheory/Core precedent):
statements are the contract, proofs fill in via the sorry-ladder workflow. Per `policy.md`
§3, proof sketches are written at skeleton time — each `sorry` corresponds to a named
sketch step. After each phase compiles: dep-graph rebuild, `/blueprint-extract`,
`blueprint_validate.py --strict`, `dataset_hygiene.py --strict`. The blueprint is
**late-bound**: extraction runs only at phase boundaries, and no blueprint LaTeX is
written by hand ahead of the Lean.

### Audit protocol (between phases)

Right after a phase's skeleton lands — statements frozen, proofs mostly `sorry` — an
**external audit** runs before the next phase begins: an LLM from a different vendor, in
a fresh context, reviews the phase's trusted surface (definitions, theorem statements,
remaining sorries) against the book, adversarially. Statement bugs are the dominant
failure mode of formalization (Lean already checks proofs) and are cheapest to fix at
this moment. Mechanics: instantiate `audits/TEMPLATE.md` as `audits/phaseN-pack.md`, hand
it plus the listed files to the auditor, record results in `audits/phaseN-findings.md`;
every finding is fixed or explicitly waived before the next phase starts. An optional
light second pass when a phase's proofs complete diffs the statements for quiet
weakening. Audits complement, not replace, in-Lean sanity theorems, which are the
machine-checked and permanent form of the same checks.

1. **Core model + classes.** Port the two vendored files to v4.25; `Finite.lean`;
   `ComputesInTime`, `decides`, `DTIME`, `P`; the oracle wrapper + trivial-oracle sanity
   theorem; PAL as an end-to-end usability check. *This phase alone unblocks future
   chapters (NP needs only these definitions).*
2. **Robustness.** Claims 1.5, 1.6, 1.8; `Composition.lean` combinators; corollary that P
   is invariant under the model tweaks. First real machine-construction proofs — builds
   the simulation vocabulary everything later reuses. The convention obligations
   recorded by the phase-1 audit are dispositioned per the phase-2 audit (findings 3
   and 13): the append-only-output and initialization bridges are **waived** (no
   read-write-output model is formalized; no exact step count is ever imported from
   [AB09]), to be revisited only if a downstream result needs a formal bridge; the
   persistent vs auto-erased query-tape statement (polynomial overhead only — constant
   overhead provably impossible) moves to the Chapter 3 oracle-class work.
3. **Encodings + universal machine.** `⌞M⌟` with totality and padding lemmas; Theorem 1.9
   in the relaxed `O(T²)` form (U simulates the one-work-tape, four-symbol normal form
   from phase 2) and the time-bounded variant.
4. **Uncomputability.** Thm 1.10 (needs only encoding + semantics; the diagonalization is
   short); Thm 1.11 (needs composition + the universal machine).
5. **Stretch — explicitly off the critical path.** §1.7's `O(T log T)` simulation;
   oblivious TMs; the RAM-TM exercise (Ex 1.9); the mathlib recursion-theory bridge.

**Blueprint reference ingestion:** ingest Chapter 1 as
`blueprint/src/references/arora-barak-ch01-*.md` (raw/clean pair, ch. 13 shows the format)
so `\statementsource`/`\proofsource` citations are possible once proofmatch runs are
approved.

## 6. Risks and honest effort assessment

- **The proof-sketch gap is the main cost.** The book proves Claims 1.5/1.6 and Thm 1.9 in
  a paragraph each; formally these are the expensive items. The AFP `Cook_Levin` entry
  spent most of its effort exactly here. `Composition.lean` is the hidden load-bearing
  file — budget for it.
- **Vendoring means drift** against a fast-moving upstream. Mitigation: minimal local
  modification, source commit recorded per file, periodic upstream diffs.
- **Definitions before theorems pays off:** phases 1–2 already give TCSlib a citable,
  blueprint-documented model of computation with P and oracles, onto which the existing
  `Complexity/NPReductions/` files can eventually be retargeted — even if phases 3–5 fill
  slowly.

## 7. Decision log

| Decision | Status |
|---|---|
| Vendor cslib `MultiTapeTM`; reuse mathlib only for `Language`/`FinEncoding`/bridge | Decided |
| Finiteness deferred in raw layer, enforced via bundled `FinTM` for all headline defs | Decided |
| Oracle wrapper lands in phase 1 (ahead of book order) | Decided |
| Work on branch `complexity/arora-barak-ch1`; verify via `scripts/lean_check.sh` (CI runs on main only) | Decided |
| Namespaces: `Turing` (vendored core) / `Complexity` (classes) | Working assumption; revisit on clash |
| NP/NTM signatures deferred to Chapter 2 work | Decided |
| §1.7 `O(T log T)` and oblivious-TM proofs are stretch goals | Decided |
| Blueprint: late-bound — generated from compiled Lean at phase boundaries only, nothing hand-written ahead of the Lean | Decided |
| External audits between phases: cross-vendor LLM with prepared packs (`audits/`), findings gate the next phase | Decided |
| Vendored cslib source commit: `a374775894efb9b7196cccf11235c60a97086dc1` (2026-09-14); relational semantics (`RelatesInSteps`) dropped in the port | Decided |
| Phase-1 audit round 1 (`audits/phase1-findings.md`): all 8 sorries confirmed true; 3 majors fixed — `TimeConstructible` repaired to `∃ c > 0, … c·(T n + 1)` (the literal exact bound refutes AB's own `id` example in this model), `OracleTM.WellFormed` added, oracle-tape constant-overhead claim corrected to polynomial; minors swept; audit-requested sanity statements added. Oracle citation is [AB09, Definition 3.4] (not 3.6) | Decided |
| Phase 1 requires a clean re-audit of the fixes before phase 2 starts | Decided |
| Phase-1 audit round 2 (`audits/phase1-reaudit-findings.md`): zero blockers/majors — all round-1 resolutions verified, all 8 new sorries confirmed true (with a worked `timeConstructible_id` witness machine reusable in the fill phase); 5 prose minors swept, blankness-certificate lemma added per note 6. **Phase-1 audit gate closed**; see `audits/phase1-resolutions.md` | Decided |
| Phase-2 renderings: Claim 1.6 rendered as **one work tape** (the merged input/work/output single-tape model is a genuinely different structure — it has an `Ω(n²)` palindrome lower bound our model beats — and is out of scope, with no identification claimed); Claim 1.8 rendered as **`NonnegativeHeads`** (our tapes are already bidirectional, so the meaningful direction is unidirectional use); obliviousness constrains input/work-head trajectories only — it does **not** force length-determined halting (phase-2 audit finding 1 refuted that with a stationary-head counterexample) and leaves emission schedules unconstrained; the `TimeConstructible` hypothesis in Exercise 1.5 is needed by the padding construction, not by the definition | Decided — audited (phase-2 round 1) |
| Output-tape/initialization convention obligations (phase-1 finding 4): **waived**, per phase-2 audit finding 3 — no formal bridge is possible without formalizing [AB09]'s read-write-output model, which this development does not do; the compensating restriction is that no exact-step-count transfer from [AB09] is ever claimed (all bounds carry existential constants, all results are self-contained in-model). The buffer-and-flush technique is documented in `Composition.lean`; a formal bridge is added only if a downstream result needs it | Decided — waiver accepted by phase-2 audit as a labeled option |
| Persistent-vs-erased query-tape polynomial-overhead statement moved from phase 2 to the Chapter 3 oracle-class work, where polynomial overhead is meaningful (class level); the impossibility of constant overhead stays documented in `Oracle.lean`. Outstanding obligation before importing any oracle-class invariance | Decided — deferral accepted by phase-2 audit (finding 13) |
| Phase-2 audit round 1 (`audits/phase2-findings.md`): 4 majors, 6 minors, 3 notes — **no theorem formula refuted**; all 11 new sorries assessed true as stated. Majors were prose/sketch-level: the false frozen-heads implication removed, the oblivious-simulation sketch replaced by the audit's corrected construction, the convention-discharge overclaim converted to the waiver above, ModelInvariance's invariance claims stated at delivered strength (alphabet: DTIME up to constants; tape count: P only). Sketch repairs: all-blank block for logical blank (1.5), tagged `Option Γ` payloads and `k = 0` case (1.6), piecewise fold coordinate with origin tags and safe-halt on non-embedded symbols (1.8). Re-audit pending | Decided |
| Fate of this file at merge (graduate to `docs/` vs. superseded by blueprint) | Open — decide at merge time |

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
6. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.

---

# ATTACHMENT C — Lean sources under audit (amended phase-2 files first, then context files)

## ===== TCSlib/Complexity/TuringMachine/Composition.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Order.Monotone.Defs
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Composition of Turing machine computations

Basic computability combinators for the bundled machines: the identity and constant
functions are linear-time computable, and time-bounded computability is closed under
composition. Composition is the load-bearing lemma of the whole development — the
universal machine (phase 3) and the `HALT` reduction (phase 4) are built from it — and
it is the part [AB09] never spells out, dispatching it with "high-level descriptions"
of machines. The Isabelle AFP `Cook_Levin` entry spends a large fraction of its effort
exactly here.

## Design

Composition is stated at the *specification* level (`ComputesFunInTime`), not as an
operator on raw machines: the composed machine is existentially produced. Internally
(proof obligation, not API) the construction simulates `M₁` with its emissions
redirected to a fresh work tape, then simulates `M₂` reading that tape in place of its
input tape.

**Convention obligation status** (phase-1 audit finding 4; phase-2 audit finding 3):
this file does *not* formally discharge the append-only vs read-write output-tape
bridge. Every statement here — hypotheses and conclusions alike — lives in the
append-only model, and [AB09]'s read-write-output machine is not formalized in this
development, so no simulation between the two conventions can even be stated yet. The
obligation is recorded in the plan's decision log as **waived**, with the compensating
restriction that no exact-step-count transfer from [AB09] is ever claimed: all bounds
carry existential constants and every result is self-contained in-model. A formal
bridge (a read-write-output machine variant plus a simulation theorem) will be added
if and only if a downstream result needs it. What this file *does* provide is the
buffer-and-flush technique — an emission can be deferred to a work tape and flushed at
the end — which is the in-model reason the append-only convention costs no generality.

## Main results

* `Complexity.TuringMachine`-level combinators (all over the binary alphabet):
  `Turing.FinTM.computesFunInTime_id`, `Turing.FinTM.computesFunInTime_const`,
  `Turing.FinTM.computesFunInTime_comp`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2-§1.3; the "high-level description"
  convention on p. 14.)
* [Balbach22] F. J. Balbach, *The Cook-Levin theorem*, Archive of Formal Proofs
  (Isabelle), 2022 — the composition-combinator architecture this file follows in
  spirit.
-/

namespace Turing.FinTM

/-- The identity function is computable in linear time.

**Proof sketch.** A zero-work-tape machine with one state: on reading an input bit,
emit that bit and move right; on reading the boundary blank, halt. It halts within
`n + 1` steps having emitted its input verbatim. -/
theorem computesFunInTime_id :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime id fun n => c * (n + 1) := by
  sorry

/-- Every constant function is computable in linear time (in fact in time `|w| + 1`,
which the stated bound dominates once `c ≥ |w| + 1`).

**Proof sketch.** A zero-work-tape machine with `|w| + 1` states `s₀, …, s_{|w|}`:
state `sᵢ` emits the `i`-th symbol of `w` and moves to `s_{i+1}`, ignoring the input;
`s_{|w|}` halts. -/
theorem computesFunInTime_const (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun _ => w) fun n => c * (n + 1) := by
  sorry

/-- **Composition.** If `f` is computable within `T₁` and `g` within a monotone `T₂`,
then `g ∘ f` is computable within `c · (T₁ n + T₂ (T₁ n) + 1)`.

The inner bound `T₂ (T₁ n)` is valid because the intermediate string is no longer than
the time that produced it: `|f x| ≤ T₁ |x|` by `Turing.MultiTapeTM.output_length_le`.
Monotonicity of `T₂` is genuinely needed to convert that length bound into a time
bound.

**Proof sketch.** Build `M` with `M₁.k + M₂.k + 1` work tapes over `Bool`. Phase one
simulates `M₁` step for step on the true input, with `M₁`'s emissions written instead
onto the dedicated intermediate tape (constant overhead per step; this is the
append-only-output buffering discussed in the module docstring). Phase two rewinds the
intermediate tape head (at most `T₁ n` steps) and simulates `M₂` step for step, with
`M₂`'s input-head reads served from the intermediate tape and `M₂`'s emissions going to
the real output tape. Phase two costs constant overhead per step of `M₂`, which halts
within `T₂ |f x| ≤ T₂ (T₁ n)` steps. Bookkeeping (phase switching, boundary detection
on the intermediate tape) is absorbed into `c`. -/
theorem computesFunInTime_comp {M₁ M₂ : FinTM Bool} {f g : List Bool → List Bool}
    {T₁ T₂ : ℕ → ℕ}
    (h₁ : M₁.ComputesFunInTime f T₁) (h₂ : M₂.ComputesFunInTime g T₂)
    (hT₂ : Monotone T₂) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (g ∘ f) fun n => c * (T₁ n + T₂ (T₁ n) + 1) := by
  sorry

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Alphabet reduction

[AB09, Claim 1.5]: a machine over any finite alphabet `Γ` is simulated by a machine
over the binary alphabet with only a constant-factor slowdown (the constant depending
on `|Γ|`), and with the same number of work tapes. This is the theorem that justifies
defining `DTIME` over binary-alphabet machines (see
`TCSlib.Complexity.ClassP.DTIME`).

## Deviations from [AB09]

* [AB09] states the slowdown as `4 log |Γ| · T(n)`; we existentialize the constant and
  pad with `+ 1` (empty input), consistently with the rest of the development.
* [AB09]'s statement fixes input and output over `{0,1}` with only the *work* alphabet
  reduced. In our model a machine has one alphabet for all tapes, so "computing a
  binary function" for a `Γ`-machine is expressed via a symbol embedding `e : Bool ↪ Γ`
  (`Turing.FinTM.ComputesFunInTimeVia`): the simulator reads genuine binary input
  directly (its table composes with `e`), block-encodes work-tape symbols in
  `⌈log₂ |Γ|⌉` bits, and decodes each emitted symbol `e b` back to the bit `b`.
  Emitted symbols are always in the range of `e` because the append-only output equals
  the final output string, which is `(f x).map e` — early emissions included, since an
  irrevocable emission remains a prefix of the final output.
* [AB09]'s Claim 1.5 hypothesizes a time-constructible `T`; the simulation does not
  need it, so we drop the hypothesis. The statement also generalizes Boolean output to
  string output.

## Main results

* `Turing.FinTM.alphabet_reduction` — [AB09, Claim 1.5].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.5, p. 16.)
-/

namespace Turing.FinTM

/-- **Alphabet reduction** [AB09, Claim 1.5]: if a machine over a finite alphabet `Γ`
computes the binary string function `f` via `e : Bool ↪ Γ` within time `T`, then a
binary-alphabet machine with the *same number of work tapes* computes `f` within
`c · (T n + 1)` for some constant `c` (depending on the original machine).

**Proof sketch.** Fix a binary block code of length `L = ⌈log₂ |Γ|⌉` for `Option Γ`'s
non-blank symbols. `M'` keeps each of `M`'s work tapes as a block-encoded tape. One
step of `M` is simulated by: reading the `L` bits under each work head into the state
(`L` steps per tape, walking right), reading the input bit directly (its `e`-image is
determined by the table), computing `M`'s transition inside the finite state, writing
back the `L`-bit codes while returning left (`L` steps per tape), moving each head `L`
cells in the simulated direction, and emitting the decoded bit whenever `M` emits.
Total: at most `c` steps of `M'` per step of `M` with `c = O(k · L)`, plus a constant
start-up. Logical blank is represented by the all-blank (`none`-cell) block — never-
visited blocks already have this shape, so no binary code needs reserving and no
initialization pass is required (phase-2 audit, finding 8). The invariant
relating block-encoded configurations to `M`'s configurations is preserved by each
simulated step, and `M`'s halting transfers. -/
theorem alphabet_reduction {Γ : Type} [Fintype Γ] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : FinTM Γ) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTimeVia e f T) :
    ∃ (c : ℕ) (M' : FinTM Bool), M'.k = M.k ∧
      M'.ComputesFunInTime f fun n => c * (T n + 1) := by
  sorry

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reduction to one work tape

[AB09, Claim 1.6]: `k` work tapes are simulated by a single work tape with a quadratic
slowdown.

## Deviations from [AB09]

* [AB09]'s Claim 1.6 merges input, work, *and output* into one single tape (the
  standard model of Sipser's text). Our model structurally always has a separate
  read-only input tape and write-only output tape, so the faithful in-model rendering
  is **one work tape**: the interesting content — interleaving `k` tapes on one, with
  marked head positions and full sweeps — is identical, while the merged-single-tape
  model itself is out of scope (it is a different structure, not an instance of
  `MultiTapeTM`).
* [AB09] states the slowdown as `5k T(n)²`; we existentialize the constant and use
  `(T n + 1)²`.
* The retained structure is a genuinely different model from [AB09]'s merged one, not
  a notational variant: with a separate input tape, palindromes are decidable in
  linear time (`TCSlib.Complexity.ClassP.Examples`), while the merged single-tape
  model has an `Ω(n²)` lower bound for them ([AB09], chapter notes, citing Maass).
  Accordingly, the theorems below are *in-model analogues* of Claim 1.6, and no
  identification with the merged model is claimed anywhere in this development
  (phase-2 audit, finding 5).

## Main results

* `Turing.FinTM.one_work_tape` — [AB09, Claim 1.6] over an enlarged alphabet.
* `Turing.FinTM.one_work_tape_binary` — combined with alphabet reduction
  ([AB09, Claim 1.5]): one work tape *and* binary alphabet, still quadratic.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.6, p. 17; Remark 1.7.)
-/

namespace Turing.FinTM

/-- **One work tape suffices** [AB09, Claim 1.6]: a `Γ`-machine computing `f` within
`T` is simulated by a machine with a single work tape, over an enlarged finite
alphabet, within `c · (T n + 1)²`.

**Proof sketch.** For `k = 0`, simulate `M` directly with one unused work tape.
For `k ≥ 1`, the single work tape of `M'` stores the `k` tapes of `M` interleaved:
cell `j·k + i` of the simulated layout holds cell `j` of tape `i` (centered at `0` in
both directions). The alphabet is enlarged to cells carrying a *tagged payload*
`Option Γ` — so a marked blank is representable, which a bare `Γ × flag` product
would miss — together with a "head here" flag and zone-boundary tags; `Γ` embeds via
`e` as an unmarked non-blank payload. To simulate one step of `M`, `M'` sweeps its work tape once
left-to-right across the visited zone recording the `k` marked symbols in its state,
computes `M`'s transition, and sweeps back right-to-left updating the marked cells and
moving the marks. After `t` steps of `M` the visited zone spans `O(k · (t + 1))`
cells, so each simulated step costs `O(k · (T n + 1))` and the total is
`c · (T n + 1)²`. Input reads and output emissions pass through unchanged. -/
theorem one_work_tape {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (f : List Γ → List Γ) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (Γ' : Type) (_ : Fintype Γ') (_ : DecidableEq Γ') (e : Γ ↪ Γ')
      (M' : FinTM Γ') (c : ℕ),
      M'.k = 1 ∧ M'.ComputesFunInTimeVia e f fun n => c * (T n + 1) ^ 2 := by
  sorry

/-- One work tape and the binary alphabet suffice simultaneously: the composition of
[AB09, Claim 1.6] with [AB09, Claim 1.5], possible because alphabet reduction
preserves the number of work tapes.

**Proof sketch.** Apply `Turing.FinTM.one_work_tape` to `M` with `Γ = Bool`,
obtaining a one-work-tape machine over some `Γ'` that computes `f` via an embedding
`Bool ↪ Γ'` within `c₁ · (T n + 1)²` — exactly the hypothesis of
`Turing.FinTM.alphabet_reduction`, which keeps `k = 1` and returns to the binary
alphabet within `c₂ · (c₁ · (T n + 1)² + 1) ≤ c · (T n + 1)²`. -/
theorem one_work_tape_binary (M : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (M' : FinTM Bool) (c : ℕ),
      M'.k = 1 ∧ M'.ComputesFunInTime f fun n => c * (T n + 1) ^ 2 := by
  sorry

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bidirectional versus unidirectional tapes

[AB09, Claim 1.8]: tapes that are infinite in both directions are simulated by tapes
infinite in one direction only, with constant-factor slowdown.

## Deviations from [AB09]

Our vendored model's tapes are *already* bidirectional (`ℤ`-indexed) — that choice is
what lets initialization dispense with start markers. So the faithful in-model
rendering of Claim 1.8 runs in the only meaningful direction: every machine is
simulated, with constant-factor slowdown and the same number of work tapes, by one
whose work heads **never visit a negative cell** (`Turing.FinTM.NonnegativeHeads`),
i.e. by a machine that uses its tapes unidirectionally. The simulating machine "folds"
each tape at the origin over the doubled alphabet `Γ × Γ`, exactly as in [AB09]'s
proof.

## Main results

* `Turing.FinTM.NonnegativeHeads` — the unidirectional-use predicate.
* `Turing.FinTM.nonnegative_heads` — [AB09, Claim 1.8].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.8, p. 18.)
-/

namespace Turing.FinTM

/-- A machine uses its work tapes unidirectionally: in every initialized run, no work
head ever visits a negative cell. -/
def NonnegativeHeads {Γ : Type} (M : FinTM Γ) : Prop :=
  ∀ (input : List Γ) (t : ℕ) (i : Fin M.k),
    0 ≤ (M.tm.runFrom (M.tm.initCfg input) t).workTapePos i

/-- **Unidirectional tapes suffice** [AB09, Claim 1.8]: a `Γ`-machine computing `f`
within `T` is simulated, with the same number of work tapes and constant-factor
slowdown, by a machine over an enlarged alphabet whose work heads never visit negative
cells.

**Proof sketch.** Fold each tape at the origin along the coordinate
`φ z = if 0 ≤ z then z else -z - 1` (note `φ 0 = φ (-1) = 0`; this is *not* the
absolute value): physical cell `φ z` holds the pair (simulated cell `z ≥ 0` in its
first component, simulated cell `-z - 1` in its second) over the alphabet of pairs,
with `Γ` embedded via `e` in the first component. The simulator's state tracks, per
tape, which component the simulated head is in. Because a transition cannot read a
head coordinate, the origin is made *detectable* by writing an origin tag into
physical cell `0` of each tape during a constant-cost initialization and preserving
it. Moves translate directly except at the fold: crossing between simulated cells `0`
and `-1` flips the component *without* issuing a physical move (the physical
coordinate stays `0`); each simulated step costs a constant number of physical steps,
giving `c · (T n + 1)` — [AB09] gets `4T`. Physical head positions are values of `φ`,
hence nonnegative; on enlarged-alphabet inputs containing symbols outside the range
of `e` — where no functional behavior is promised but `NonnegativeHeads` still
quantifies — the simulator halts safely on first contact, preserving nonnegativity
(phase-2 audit, finding 10 and case A14). The folding invariant transfers computation
and halting on embedded inputs. -/
theorem nonnegative_heads {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (f : List Γ → List Γ) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (Γ' : Type) (_ : Fintype Γ') (_ : DecidableEq Γ') (e : Γ ↪ Γ')
      (M' : FinTM Γ') (c : ℕ),
      M'.NonnegativeHeads ∧ M'.k = M.k ∧
        M'.ComputesFunInTimeVia e f fun n => c * (T n + 1) := by
  sorry

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.ClassP.TimeConstructible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious machines

A machine is *oblivious* if its head movements depend only on the input length, not on
the input itself [AB09, Remark 1.7 and Exercise 1.5]. Obliviousness will matter for
the Cook-Levin theorem (Chapter 2), where the tableau of an oblivious computation has
input-independent structure.

## Design

* Configurations are indexed by their input, so head positions of runs on different
  inputs live in different types only for the input head; obliviousness compares
  `Fin`-valued input positions through `ℕ` and work positions (in `ℤ`) directly.
* `Oblivious` constrains *represented* head trajectories only — the input head and
  the work heads. Our model has no output-head position (output is an append-only
  stream), so emission schedules are deliberately unconstrained; [AB09]'s read-write
  output head is covered by this reading only via a bridge, e.g. a machine that emits
  once at a fixed final time, as the decider produced below does.
* `Oblivious` does **not** imply that the halting time is determined by the input
  length: heads freeze on halting, but frozen positions can coincidentally agree — a
  stationary-head machine can halt after one or two steps depending on its first
  input bit while satisfying `Oblivious` (phase-2 audit, finding 1, with an explicit
  counterexample in `audits/phase2-findings.md`). The `TimeConstructible` hypothesis
  below is required by the *construction* (the simulator derives a length-determined
  step budget and pads its schedule to it), not forced by the definition. If a
  downstream use (the Cook-Levin tableau, Ch. 2) needs length-determined halting or a
  simultaneous one-work-tape oblivious normal form (`M.k = 1 ∧ M.Oblivious`), those
  are separate conjuncts for that normal-form theorem.
* We state the quadratic version — Exercise 1.5's *first assertion*, adapted to this
  model; the exercise's final two-tape normal form is **not** included here. The
  `O(T log T)` sharpening (Exercise 1.6) is a stretch goal alongside §1.7, off the
  critical path.

## Main definitions

* `Turing.FinTM.Oblivious` — [AB09, Remark 1.7].

## Main results

* `Complexity.oblivious_of_mem_DTIME` — [AB09, Exercise 1.5]: every language decidable
  in time-constructible time `T` is decided by an oblivious machine in `O((T + 1)²)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Remark 1.7, p. 17; Exercise 1.5, p. 34.)
-/

namespace Turing.FinTM

/-- A machine is *oblivious* if, at every step, its head positions on two inputs of
the same length agree: they are a function of the input length and the time only.
[AB09, Remark 1.7] -/
def Oblivious {Γ : Type} (M : FinTM Γ) : Prop :=
  ∀ (x y : List Γ), x.length = y.length → ∀ t : ℕ,
    (((M.tm.runFrom (M.tm.initCfg x) t).inputPos : ℕ) =
      ((M.tm.runFrom (M.tm.initCfg y) t).inputPos : ℕ)) ∧
    (M.tm.runFrom (M.tm.initCfg x) t).workTapePos =
      (M.tm.runFrom (M.tm.initCfg y) t).workTapePos

end Turing.FinTM

namespace Complexity

open Turing

/-- **Oblivious simulation** — the first assertion of [AB09, Exercise 1.5], adapted
to this model: for time-constructible `T`, every language in `DTIME T` is decided by
an *oblivious* machine within `c · (T n + 1)²`. (The exercise's additional two-tape
normal form is not part of this statement.)

**Proof sketch** (corrected per the phase-2 audit, finding 2: the construction must
not invoke `one_work_tape_binary` per simulated step — that composes quadratics into
a quartic — must not run the constructibility witness verbatim, which need not be
oblivious, and must park the real input head). Take a decider for `L` within
`a · T n` and a constructibility witness within `b · (T n + 1)`.

1. Run the witness with every non-blank input symbol *read as `false`* (substituted
   in its transition table): its entire run — trajectories, emissions, halting time —
   then coincides with its run on the all-`false` input of length `n`, hence depends
   only on `n`, and it still computes `⌞T n⌟`; store the budget on a work tape.
2. Copy the real input to a work tape in one fixed scan and rewind (cost
   `O(n + 1)`, absorbed since `n ≤ T n`), then park the real input head for good.
3. Set `B n = (a + 1) · (T n + 1)` macrosteps and prepare a marked layout of size
   `O(B n)` holding the decider's work tapes, the virtual input copy, virtual head
   markers, and a step counter.
4. Each macrostep simulates one step of the decider by a fixed number of full sweeps
   of the layout — tape data affects writes, simulated state, and markers, never the
   sweep path or its duration — idling identically once the simulated machine halts,
   for exactly `B n` macrosteps (counter maintenance within the per-macrostep linear
   allowance; fixed-duration binary block coding throughout, so no appeal to the
   existential `alphabet_reduction` is needed to stay binary and oblivious).
5. Emit the stored answer bit at a fixed final time and halt.

Every head trajectory and the halting time are then functions of `n` and `t` alone,
and the total cost is `O(b · (T n + 1) + (B n)²) = O((T n + 1)²)`. -/
theorem oblivious_of_mem_DTIME {L : Language Bool} {T : ℕ → ℕ}
    (hT : TimeConstructible T) (hL : L ∈ DTIME T) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.Oblivious ∧ M.DecidesInTime L fun n => c * (T n + 1) ^ 2 := by
  sorry

end Complexity
```

## ===== TCSlib/Complexity/ClassP/ModelInvariance.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape
import TCSlib.Complexity.ClassP.P

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# "And why it doesn't matter": model invariance of DTIME and P

The payoff of the robustness theorems ([AB09, §1.3.1], formalized in
`TCSlib.Complexity.TuringMachine.Robustness`), stated at the strength the theorems
actually deliver (phase-2 audit, finding 4): **alphabet size** never matters —
`DTIME` is alphabet-invariant, the alphabet-dependent constant being absorbed by
`DTIME`'s own existential — while **the number of work tapes** does not matter *for
`P`*, where the quadratic overhead of tape reduction is harmless. No invariance of a
fixed class `DTIME T` under tape reduction is claimed, and [AB09, §1.6.1] likewise
draws only the polynomial-time conclusion. This is the formal content of the
chapter's title at class level.

## Main definitions

* `Turing.FinTM.DecidesInTimeVia` — a machine over a larger alphabet decides a binary
  language via a symbol embedding.

## Main results

* `Complexity.mem_DTIME_of_decidesInTimeVia` — deciding over any finite alphabet lands
  in binary `DTIME` (constant absorbed). [AB09, Claim 1.5 for languages]
* `Complexity.mem_P_of_decidesInTimeVia_poly` — `P` is alphabet-invariant.
* `Complexity.mem_P_iff_one_work_tape` — `P` is exactly what one-work-tape binary
  machines decide in polynomial time. [AB09, Claims 1.5-1.6 for `P`]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3.1; §1.6.1 "Why the model may not matter".)
-/

namespace Turing.FinTM

/-- The machine `M`, over alphabet `Γ`, decides the binary language `L` via the symbol
embedding `e : Bool ↪ Γ` within time `T`: on every input `x.map e` it halts within
`T |x|` steps with output `[e b]` where `b` is the membership bit of `x` in `L`. -/
def DecidesInTimeVia {Γ : Type} (M : FinTM Γ) (e : Bool ↪ Γ) (L : Language Bool)
    (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime (x.map e)
      [e (MultiTapeTM.indicator (L : Set (List Bool)) x)] (T x.length)

end Turing.FinTM

namespace Complexity

open Turing

/-- Deciding a language over *any* finite alphabet puts it in the binary-machine class
`DTIME` (with the alphabet-dependent constant absorbed by `DTIME`'s existential).

**Proof sketch.** `DecidesInTimeVia` is `ComputesFunInTimeVia` for the function
`x ↦ [indicator L x]` (note `[b].map e = [e b]`); apply
`Turing.FinTM.alphabet_reduction` and absorb its constant `c` into `DTIME`'s. -/
theorem mem_DTIME_of_decidesInTimeVia {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : FinTM Γ} {L : Language Bool} {T : ℕ → ℕ}
    (h : M.DecidesInTimeVia e L T) :
    L ∈ DTIME fun n => T n + 1 := by
  sorry

/-- **`P` is alphabet-invariant**: a language decided in polynomial time by a machine
over any finite alphabet is in `P`.

**Proof sketch.** `Complexity.mem_DTIME_of_decidesInTimeVia` gives
`L ∈ DTIME (C · (n + 1) ^ d + 1)`; conclude with `Complexity.mem_P_of_dtime_le`
(pointwise bound `C · (n + 1) ^ d + 1 ≤ (C + 1) · 2 ^ d · (n ^ d + 1)`, using
`(n + 1) ^ d ≤ 2 ^ d (n ^ d + 1)` from the `mem_P_iff` arithmetic). -/
theorem mem_P_of_decidesInTimeVia_poly {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : FinTM Γ} {L : Language Bool} (C d : ℕ)
    (h : M.DecidesInTimeVia e L fun n => C * (n + 1) ^ d) :
    L ∈ P := by
  sorry

/-- **`P` is tape-count-invariant**: `P` is exactly the class of languages decided by
binary machines with a *single* work tape in polynomial time. [AB09, Claim 1.6 at the
level of `P`; quadratic slowdown preserves polynomiality]

**Proof sketch.** Backward: a one-work-tape polynomial decider is in particular a
polynomial decider (`Complexity.mem_P_iff`). Forward: from `mem_P_iff` take a decider
within `C · (n + 1) ^ d`; `DecidesInTime` is `ComputesFunInTime` for
`x ↦ [indicator L x]`, so `Turing.FinTM.one_work_tape_binary` yields a one-work-tape
binary machine within `c · (C · (n + 1) ^ d + 1)² ≤ C' · (n + 1) ^ (2d)`, again of the
`mem_P_iff` shape. -/
theorem mem_P_iff_one_work_tape {L : Language Bool} :
    L ∈ P ↔ ∃ (M : FinTM Bool) (C d : ℕ),
      M.k = 1 ∧ M.DecidesInTime L fun n => C * (n + 1) ^ d := by
  sorry

end Complexity
```

## ===== TCSlib/Complexity/TuringMachine/Finite.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.Basic
import TCSlib.Complexity.TuringMachine.Deterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bundled finite Turing machines

The raw model `Turing.MultiTapeTM k Symbol State` deliberately does not require `Symbol` or
`State` to be finite: semantics, simulations, and resource counting do not need it, and
compound state types arise freely in constructions. Finiteness is nevertheless
mathematically essential for complexity theory — with infinitely many states a machine can
memorize its whole input in the state and decide any language in linear time, and an
infinite transition table has no string encoding.

This file provides the bundled layer `Turing.FinTM`: a machine together with `Fintype` and
`DecidableEq` instances for its state type. All headline definitions of the Chapter 1
development (`DTIME`, `P`, machine encodings, the universal machine) are stated exclusively
over `FinTM`, so the finiteness hypothesis can never be dropped by accident. The instances
are carried as *data* (not `Finite` propositions) because the machine-encoding function
`⌞M⌟` must enumerate the transition table.

The alphabet parameter `Symbol` stays explicit and unbundled: the Chapter 1 headline
definitions fix `Symbol := Bool` (see `TCSlib.Complexity.ClassP.DTIME`), and results that
need a finite alphabet for a general `Symbol` take `[Fintype Symbol]` hypotheses at use
sites.

## Main definitions

* `Turing.FinTM Symbol` — a multi-tape TM over alphabet `Option Symbol` with a bundled
  finite state type. [AB09, §1.2]
* `Turing.FinTM.ComputesInTime` — the machine halts on `input` within `t` steps with
  `output` on the output tape (time-only variant of
  `Turing.MultiTapeTM.ComputesInTimeAndSpace`). [AB09, Definition 1.3]
* `Turing.FinTM.ComputesFunInTime` — the machine computes `f` in time `T`.
  [AB09, Definition 1.3]

## Main results

* `Turing.FinTM.ComputesInTime.mono` — halting is absorbing, so the time bound can be
  weakened.
* `Turing.FinTM.not_computesInTime_zero` — no machine computes anything in zero steps
  (the initial state is not the halting state).
* `Turing.MultiTapeTM.output_length_le`, `Turing.MultiTapeTM.output_prefix` — raw-layer
  output lemmas (at most one symbol is emitted per step, and output only grows), stated
  here rather than in the vendored `Deterministic.lean` to keep the vendored files
  unmodified.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, §1.3.)
-/

namespace Turing

/-!
### Raw-layer output lemmas

Additions on top of the vendored files (kept here so the vendored `Deterministic.lean`
stays byte-comparable with upstream).
-/

namespace MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The output of an initialized run after `t` steps has length at most `t`: each step
appends at most one symbol.

**Proof sketch.** Induction on `t` with `Turing.MultiTapeTM.runFrom_succ_eq_step'` and
`Turing.MultiTapeTM.step_output` (`Option.toList` has length at most one); the initial
output is `[]`. -/
theorem output_length_le (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    ((tm.runFrom (tm.initCfg input) t).output).length ≤ t := by
  sorry

/-- Output is monotone along a run: the output at an earlier time is a prefix of the
output at any later time.

**Proof sketch.** It suffices to treat one step (`Turing.MultiTapeTM.step_output`: a
step appends), then induct on the difference using
`Turing.MultiTapeTM.runFrom_add` and transitivity of `List.IsPrefix`. -/
theorem output_prefix (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    {t t' : ℕ} (h : t ≤ t') :
    (tm.runFrom cfg t).output <+: (tm.runFrom cfg t').output := by
  sorry

end MultiTapeTM

/-- A multi-tape Turing machine over the alphabet `Option Symbol` bundled with a finite
state type. This is the machine of [AB09, §1.2] up to the declared model variations
(append-only output tape, start-marker-free initialization — see the deviations list in
`TCSlib.Complexity.ClassP.DTIME`): the raw `MultiTapeTM` is internal plumbing, and
every headline complexity-theoretic definition is stated over `FinTM`.

The instances are data (`Fintype`/`DecidableEq`, not `Finite`) because encoding a machine
as a string requires enumerating its transition table. -/
structure FinTM (Symbol : Type) : Type 1 where
  /-- number of work tapes -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible, needed to tabulate the transition function -/
  [decEqState : DecidableEq State]
  /-- the underlying machine -/
  tm : MultiTapeTM k Symbol State

namespace FinTM

attribute [instance] FinTM.fintypeState FinTM.decEqState

variable {Symbol : Type}

/-- The machine `M` halts on `input` within `t` steps with `output` written on its output
tape. Time-only variant of `Turing.MultiTapeTM.ComputesInTimeAndSpace` (the space used is
existentially discarded). [AB09, Definition 1.3] -/
def ComputesInTime (M : FinTM Symbol) (input output : List Symbol) (t : ℕ) : Prop :=
  ∃ s, M.tm.ComputesInTimeAndSpace input output t s

/-- The machine `M` computes the string function `f`, halting within `T |input|` steps on
every input. [AB09, Definition 1.3: "M computes f in T(n)-time"] -/
def ComputesFunInTime (M : FinTM Symbol) (f : List Symbol → List Symbol) (T : ℕ → ℕ) : Prop :=
  ∀ input : List Symbol, M.ComputesInTime input (f input) (T input.length)

/-- The machine `M`, over alphabet `Γ`, computes the string function `f` on `α`-strings
*via* the symbol embedding `e : α ↪ Γ`: on every input `x.map e` it halts within
`T |x|` steps with `(f x).map e` on its output tape. This is how a machine over a
larger alphabet is said to compute a function on a smaller one; it is the interface of
the alphabet-robustness results [AB09, §1.3.1]. -/
def ComputesFunInTimeVia {α Γ : Type} (M : FinTM Γ) (e : α ↪ Γ)
    (f : List α → List α) (T : ℕ → ℕ) : Prop :=
  ∀ x : List α, M.ComputesInTime (x.map e) ((f x).map e) (T x.length)

/-- Halting is absorbing, so a time bound can be weakened: if `M` produces `output`
within `t` steps it also does so within any `t' ≥ t` steps.

**Proof sketch.** By `Turing.MultiTapeTM.runFrom_add` the run to step `t'` factors through
step `t`; the state there is `none`, so `Turing.MultiTapeTM.runFrom_of_halt` shows the
configuration no longer changes, and in particular state and output at step `t'` agree with
step `t`. The space used up to step `t'` exists (it is whatever `spaceUsed` evaluates to),
which discharges the existential. -/
theorem ComputesInTime.mono {M : FinTM Symbol} {input output : List Symbol} {t t' : ℕ}
    (h : M.ComputesInTime input output t) (hle : t ≤ t') :
    M.ComputesInTime input output t' := by
  sorry

/-- No machine computes anything in zero steps: the initial configuration is in the
initial state, which is not the halting state. In particular a time budget of `0`
(e.g. from a vanishing time bound) is never satisfiable. -/
theorem not_computesInTime_zero (M : FinTM Symbol) (input output : List Symbol) :
    ¬M.ComputesInTime input output 0 := by
  rintro ⟨s, hhalt, -⟩
  simp [MultiTapeTM.runFrom_zero] at hhalt

end FinTM

end Turing
```

## ===== TCSlib/Complexity/ClassP/DTIME.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deciding languages and the classes DTIME

Languages are sets of binary strings, `Mathlib`'s `Language Bool`. A bundled finite
machine over the binary alphabet (`Turing.FinTM Bool`, tape alphabet
`Option Bool = {0, 1, blank}`) *decides* a language `L` in time `T` if on every input `x`
it halts within `T |x|` steps with the single-symbol output `[true]` if `x ∈ L` and
`[false]` otherwise. `DTIME T` is the class of languages decided in time `c · T` for some
constant `c`. [AB09, §1.6, Definition 1.12]

## Design and deviations from [AB09]

* [AB09] fixes the four-symbol alphabet `{▷, □, 0, 1}` for the definition and remarks the
  choice is immaterial. Our machines use the three-symbol tape alphabet
  `Option Bool = {0, 1, blank}` over bidirectional tapes, which need no start symbol
  ([AB09, Claim 1.8] direction). The alphabet-reduction theorem ([AB09, Claim 1.5],
  phase 2) will show that machines over any finite alphabet are simulated by binary ones
  with a constant-factor slowdown — absorbed by the `∃ c` in `DTIME` — so defining
  `DTIME` over binary machines loses no generality.
* Acceptance is by output (`[true]`/`[false]`), not by accepting states: the vendored
  model has a single halting state and distinguishes outcomes by output, which [AB09]
  does via the output tape as well.
* **The output tape is append-only** (the transition emits at most one symbol per step,
  and emitted symbols cannot be erased), whereas [AB09, §1.2] designates a read-write
  work tape as the output tape — [AB09, p. 19] itself lists write-only output among the
  benign model variations. The simulation (an extra work tape holding the tentative
  output, copied out before halting, with constant-factor overhead) is a phase-2
  obligation; until then, exact step counts must not be transported between the two
  conventions.
* **Initialization differs from [AB09]**: there are no start-marker (`▷`) cells — the
  bidirectional tapes make them unnecessary — and the input head begins on the first
  input symbol (on the boundary blank for empty input), with all work tapes blank.
* The constant `c` ranges over all of `ℕ`; `c = 0` yields the bound `0`, within which no
  machine can halt (the initial state is not the halting state), so it contributes
  nothing — this matches [AB09]'s `c > 0` without carrying a positivity side condition.

## Main definitions

* `Turing.FinTM.DecidesInTime` — `M` decides `L` within time `T`. [AB09, §1.6 with
  Definition 1.3]
* `Complexity.DTIME` — the class of languages decidable in time `c · T`.
  [AB09, Definition 1.12]

## Main results

* `Complexity.DTIME.mono` — `DTIME` is monotone in the time bound.
* `Complexity.DTIME_eq_empty_of_exists_zero` — a time bound that vanishes at some
  length has an empty class (every machine needs at least one step to halt).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definitions 1.3, 1.12.)
-/

namespace Turing.FinTM

/-- The machine `M` decides the language `L` within time `T`: on every input `x` it halts
within `T |x|` steps with output `[true]` if `x ∈ L` and `[false]` otherwise.
[AB09, §1.6 with Definition 1.3] -/
def DecidesInTime (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length)

end Turing.FinTM

namespace Complexity

open Turing

/-- The class of languages decidable in time `c · T` for some constant `c`: a language
`L` is in `DTIME T` iff some finite binary-alphabet multi-tape machine decides it within
`c · T n` steps on inputs of length `n`. [AB09, Definition 1.12] -/
def DTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n}

/-- `DTIME` is monotone in the time bound.

**Proof sketch.** A machine deciding `L` within `c · T₁ n` steps also halts (with the
same output) within `c · T₂ n ≥ c · T₁ n` steps, by `Turing.FinTM.ComputesInTime.mono`
(halting is absorbing). -/
theorem DTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : DTIME T₁ ⊆ DTIME T₂ := by
  sorry

/-- If the time bound vanishes at even one input length, the class is empty: the
initial state is not the halting state, so no machine halts in `c · 0 = 0` steps on an
input of that length (e.g. `List.replicate n false`).

**Proof sketch.** Given `T n = 0` and a claimed decider, instantiate `DecidesInTime` at
the input `List.replicate n false`; the budget is `c * T n = 0`, contradicting
`Turing.FinTM.not_computesInTime_zero`. -/
theorem DTIME_eq_empty_of_exists_zero {T : ℕ → ℕ} (h : ∃ n, T n = 0) : DTIME T = ∅ := by
  sorry

end Complexity
```

## ===== TCSlib/Complexity/ClassP/TimeConstructible.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Time-constructible functions

A function `T : ℕ → ℕ` is *time constructible* if `T n ≥ n` and some machine computes,
on every input `x`, the binary representation of `T |x|` within at most
`c · (T |x| + 1)` steps for a positive constant `c`. [AB09, §1.3, with the audit-mandated
budget repair below.] Time constructibility rules out pathological time bounds. It is
needed when a machine must *generate* a step budget from its input length, as in the
hierarchy theorems; note that the timed universal machine of [AB09, p. 21] receives its
budget as an explicit extra input and needs no constructibility hypothesis.

## Design and deviations from [AB09]

* Binary representation is `Nat.bits` (little-endian, no leading `false`s), where [AB09]
  writes `⌞T(|x|)⌟` without fixing endianness. Nothing in Chapter 1 depends on the choice.
* **Deviation (audit-mandated).** [AB09] demands the computation run within exactly
  `T n` steps and then asserts that `n`, `n log n`, `n²`, `2ⁿ` are time constructible.
  The phase-1 external audit (`audits/phase1-findings.md`, finding 1, adversarial cases
  5-6) *proved the literal reading false in this model*: under the exact bound, the
  identity function — [AB09]'s own first example — is not time constructible (on the
  budget `T n = n`, the first transition on `[false]` and `[false, false]` is the same
  function call, and the length-1 budget forces it to halt with output `[true]`, which
  absorption then freezes at length 2), and even `T n = n + 1` fails by an append-only
  prefix argument. We therefore allow a positive constant factor on `T n + 1`, which
  suffices for every downstream use and restores the book's examples *after small-input
  normalization*: the literal `n · ⌈log₂ n⌉`, for instance, still violates `T n ≥ n` at
  `n = 1`, so such examples are stated with a `max`-with-`n` or `+ 1` normalization.
  Exact constants in downstream results must be derived from this form, not inherited
  from the strict reading.

## Main definitions

* `Complexity.TimeConstructible` — [AB09, §1.3], with the constant-slack repair above.

## Main results

* `Complexity.timeConstructible_id` — the identity function is time constructible,
  restoring [AB09]'s example under the repaired definition.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3, "Time-constructible functions".)
-/

namespace Complexity

open Turing

/-- `T` is time constructible: `T n ≥ n`, and some finite binary machine computes
`x ↦ ⌞T |x|⌟` (binary via `Nat.bits`) within `c · (T |x| + 1)` steps for a positive
constant `c`. [AB09, §1.3], with the constant-slack deviation documented in the module
docstring (the literal exact-`T n` bound is refuted in this model by
`audits/phase1-findings.md`, finding 1). -/
def TimeConstructible (T : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ T n) ∧
  ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool, ∀ x : List Bool,
    M.ComputesInTime x (T x.length).bits (c * (T x.length + 1))

/-- The identity function is time constructible. [AB09, §1.3 examples]

**Proof sketch.** A one-work-tape machine maintains a little-endian binary counter on
its work tape while scanning the input left to right: for each input symbol it
increments the counter (walking right over `true` cells turning them `false` until the
first `false`/blank cell, which becomes `true`, then returning to cell 0). Incrementing
`n` times costs amortized `O(1)` per increment, `O(n)` in total. When the input head
reads the blank past the input, the machine walks the counter left to right emitting
each bit to the output tape (`O(log n)` steps) and halts. The total is at most
`c · (n + 1)` steps for an absolute constant `c`, and the emitted string is `n.bits`
(for `n = 0` the counter region is empty and nothing is emitted, matching
`Nat.bits 0 = []`). -/
theorem timeConstructible_id : TimeConstructible id := by
  sorry

end Complexity
```

## ===== TCSlib/Complexity/ClassP/P.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.DTIME

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class P

`P` is the class of languages decidable in polynomial time: the union over `c` of
`DTIME (n^c + 1)`. [AB09, Definition 1.13, with the `+ 1` padding explained below —
every *positive*-degree component of the literal unpadded union is empty in this model,
since `n^c` vanishes at `n = 0` and no machine halts in zero steps; [AB09]'s union
ranges over `c ≥ 1`, so its literal reading is empty, while including degree `0` would
give exactly `DTIME 1` (in Lean `0 ^ 0 = 1`).]

## Design and deviations from [AB09]

* We take the union of `DTIME (fun n => n ^ c + 1)` over all `c : ℕ` where [AB09] writes
  `⋃_{c ≥ 1} DTIME(n^c)`. The `+ 1` repairs the empty-input degeneracy: a machine needs
  at least one step to halt, so for the degrees `d ≥ 1` of [AB09]'s union no language
  whatsoever is decided within `c · 0^d = 0` steps on the empty input, and the literal
  [AB09] definition would (vacuously) exclude even constant-time machines on that input. For `n ≥ 1` the bounds `c · (n^d + 1)` and
  `c' · n^d` sandwich each other, so this is the standard reading of the same class.
  Ranging over `c = 0` too is harmless: `n^0 + 1 = 2` is a constant bound, subsumed by
  larger `c`.

## Main definitions

* `Complexity.P` — [AB09, Definition 1.13].

## Main results

* `Complexity.dtime_poly_subset_P` — each `DTIME (n^c + 1)` is contained in `P`.
* `Complexity.mem_P_iff` — `P` is exactly the class decidable within `C · (n + 1) ^ d`
  for some constants, certifying that the `+ 1` padding has the conventional
  polynomial-time content.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definition 1.13.)
-/

namespace Complexity

open Turing

/-- The class of polynomial-time decidable languages:
`P = ⋃ c, DTIME (n^c + 1)`. [AB09, Definition 1.13] -/
def P : Set (Language Bool) := ⋃ c : ℕ, DTIME fun n => n ^ c + 1

/-- Every fixed-degree polynomial time class is contained in `P`. -/
theorem dtime_poly_subset_P (c : ℕ) : DTIME (fun n => n ^ c + 1) ⊆ P :=
  Set.subset_iUnion (fun c : ℕ => DTIME fun n => n ^ c + 1) c

/-- Membership in `P` from a concrete polynomial bound: if `L` is decidable within any
time bound that is pointwise dominated by a polynomial, then `L ∈ P`. (Pointwise, not
eventual, domination: an eventual-bound variant follows with the *same machine* by
absorbing the finitely many exceptional bounds into the constant, and is deferred.)

**Proof sketch.** Pick `c` and `d` with `T n ≤ c * (n ^ d + 1)` for all `n`. By
`Complexity.DTIME.mono`, `DTIME T ⊆ DTIME (fun n => c * (n ^ d + 1))`; the latter equals
a subclass of `DTIME (fun n => n ^ d + 1)` because the constant `c` is absorbed by the
existential constant in the definition of `DTIME` (the two constants multiply). Conclude
with `Complexity.dtime_poly_subset_P`. -/
theorem mem_P_of_dtime_le {L : Language Bool} {T : ℕ → ℕ}
    (hL : L ∈ DTIME T) (c d : ℕ) (hT : ∀ n, T n ≤ c * (n ^ d + 1)) : L ∈ P := by
  sorry

/-- `P` is exactly the class of languages decidable within `C · (n + 1) ^ d` steps for
some constants `C` and `d`. This certifies that the `+ 1` padding in the definition of
`P` has the conventional polynomial-time content.

**Proof sketch.** Forward: a witness for the degree-`c` component gives a bound
`a · (n ^ c + 1) ≤ 2a · (n + 1) ^ c`. Backward: `(n + 1) ^ d ≤ 2 ^ d · (n ^ d + 1)`
(check `n = 0` directly; for `n ≥ 1` use `n + 1 ≤ 2n`), so a `C · (n + 1) ^ d` decider
is a `(C · 2 ^ d) · (n ^ d + 1)` decider, landing in the degree-`d` component.
(`audits/phase1-findings.md`, "Polynomial-time normalization".) -/
theorem mem_P_iff {L : Language Bool} :
    L ∈ P ↔ ∃ (C d : ℕ) (M : FinTM Bool),
      M.DecidesInTime L fun n => C * (n + 1) ^ d := by
  sorry

/-- Constant time is polynomial time.

**Proof sketch.** `Complexity.mem_P_of_dtime_le` with `T = fun _ => 1`, `c = 1`,
`d = 1`, since `1 ≤ 1 * (n ^ 1 + 1)`. -/
theorem dtime_one_subset_P : DTIME (fun _ => 1) ⊆ P := by
  sorry

end Complexity
```

## ===== TCSlib/Complexity/ClassP/Examples.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.P

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Example: palindromes are decidable in linear time

The language `PAL` of binary palindromes is decidable in linear time, hence in `P`.
[AB09, Examples 1.1 and 1.4] This is the phase-1 sanity check that the model and class
definitions are *usable*: proving it requires constructing a concrete machine and running
the definitional semantics on it end to end.

## Deviations from [AB09]

* [AB09, Example 1.1] states "within `3n` steps". We state `PAL ∈ DTIME (n + 1)`: the
  `∃ c` in `DTIME` absorbs the leading constant, and the `+ 1` covers the empty input, on
  which every machine needs at least one step to halt (`3 · 0 = 0` is unachievable — the
  book ignores this degenerate case).

## Main definitions

* `Complexity.PAL` — the palindrome language. [AB09, Example 1.1]

## Main results

* `Complexity.PAL_mem_DTIME_linear` — `PAL ∈ DTIME (n + 1)`. [AB09, Example 1.4]
* `Complexity.PAL_mem_P` — `PAL ∈ P`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Examples 1.1, 1.4.)
-/

namespace Complexity

open Turing

/-- The language of binary palindromes. [AB09, Example 1.1] -/
def PAL : Language Bool := {x | x.reverse = x}

/-- Palindromes are decidable in linear time. [AB09, Examples 1.1 and 1.4]

**Proof sketch.** Adapt the machine of [AB09, Example 1.1] to our model (bidirectional
tapes, no start symbol, blank = `none`): a one-work-tape machine with states
`{copy, rewind, test}`.

1. *Copy* (`n + 1` steps): move the input head and the work head right in unison, copying
   each input symbol to the work tape, until the input head reads blank (one cell past the
   input). The work head now sits one cell right of the copied string.
2. *Rewind* (`n + 1` steps): move the input head left back to the left boundary cell while
   the work head stays put; then step the work head one cell left onto the last symbol.
3. *Test* (`n + 1` steps): move the input head right and the work head left in unison,
   comparing the input symbol against the work symbol. On a mismatch, emit `false` and
   halt. When the input head reads blank again (all positions matched), emit `true` and
   halt.

Each phase takes at most `n + 1` steps, so some constant `c` (e.g. `c = 4`) gives
`c · (n + 1) ≥ 3n + 3` total steps, witnessing the `DTIME (n + 1)` bound. The formal
proof constructs the machine's transition function explicitly and establishes the
three-phase invariants by induction on the step count. -/
theorem PAL_mem_DTIME_linear : PAL ∈ DTIME fun n => n + 1 := by
  sorry

/-- Palindromes are decidable in polynomial time.

**Proof sketch.** `Complexity.PAL_mem_DTIME_linear` with
`Complexity.mem_P_of_dtime_le`, using `n + 1 ≤ 1 * (n ^ 1 + 1)`. -/
theorem PAL_mem_P : PAL ∈ P := by
  sorry

end Complexity
```

## ===== TCSlib/Complexity/TuringMachine/Oracle.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.TuringMachine.Deterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oracle Turing machines

An oracle Turing machine [AB09, §3.4, Definition 3.4; pulled forward to Chapter 1 to
validate the model architecture] is a multi-tape machine with one additional designated
*query tape* and three designated states `qQuery`, `qYes`, `qNo`. Whenever the machine
enters `qQuery`, the string currently written on the query tape is submitted to the oracle
`O`: in a single step the machine moves to `qYes` if the query is in `O` and to `qNo`
otherwise, with all tapes and heads unchanged.

## Design

This file is the architectural test of the `Action`/`Action.apply` split: an oracle machine
reuses the configurations `Turing.Cfg (k + 1)` (the query tape is the extra work tape, at
index `Fin.last k`) and the action application of the plain model, and differs *only* in how
the next action is chosen — the step function is parametrized by the oracle
`O : Language Symbol`. Time and space measures therefore transfer unchanged.

Definitional choices worth auditing:

* **The query string** (`OracleTM.queryString`) is read from cell `0` of the query tape
  rightward up to (excluding) the first blank cell; if the whole nonnegative half-tape is
  blank-free (possible for an arbitrary configuration, though not for one reachable from an
  initial configuration), the query is defined to be `[]`. [AB09] leaves the extraction
  convention implicit; this is one concrete faithful reading.
* **The answer step** changes only the state; heads and tapes stay put. Some texts
  instead erase the query tape on each answer. The two conventions are equivalent up to
  *polynomial* overhead, but **not** constant overhead: computing the parity of `n`
  distinct length-`n` queries takes `O(n)` steps with a persistent tape and `Ω(n²)`
  steps with auto-erasure (`audits/phase1-findings.md`, finding 3, case 12).
  Consequently, exact `DTIME`-level bounds must never be transferred across this
  convention; class-level results (`Pᴼ` etc.) are unaffected.
* `qYes`/`qNo` are ordinary states from the machine's point of view (its transition
  function handles them); only `qQuery` triggers special behavior. The machine may query
  repeatedly. This reading presumes the three special states are pairwise distinct,
  which the raw structure does not enforce (e.g. with `qYes = qQuery` the machine
  re-queries forever after a positive answer): results at the faithful interface assume
  `OracleTM.WellFormed`. Note that
  `q₀ = qQuery` is legitimate and deliberately allowed (the machine then submits the
  empty query on its first step).

## Main definitions

* `Turing.OracleTM` — the oracle machine. [AB09, Definition 3.4]
* `Turing.OracleTM.WellFormed` — the three special states are pairwise distinct; the
  standing hypothesis of the faithful interface (oracle complexity classes will require
  it).
* `Turing.OracleTM.step`, `Turing.OracleTM.runFrom` — semantics relative to an oracle.
* `Turing.OracleTM.ComputesInTime` — output and time bound relative to an oracle.
* `Turing.Action.extend`, `Turing.Action.mapState`, `Turing.Cfg.embedOracle`,
  `Turing.OracleTM.ofMultiTapeTM` — the embedding of plain machines as oracle machines
  that never query.
* `Turing.OracleTM.plainEmptyOracle` — the converse direction: an oracle machine run
  with the empty oracle, as a plain `k + 1`-tape machine in exact lockstep.

## Main results (sanity checks for the architecture)

* `Turing.OracleTM.step_eq_of_ne_qQuery` — away from `qQuery`, the step does not depend
  on the oracle.
* `Turing.OracleTM.ofMultiTapeTM_wellFormed` — the embedding produces well-formed
  machines.
* `Turing.OracleTM.runFrom_ofMultiTapeTM` — an embedded plain machine runs in lockstep
  with the original, under every oracle.
* `Turing.OracleTM.computesInTime_ofMultiTapeTM` — hence its input/output behavior and
  time bounds are oracle-independent and agree with the plain machine's.
* `Turing.OracleTM.runFrom_plainEmptyOracle` — the empty-oracle elimination runs in
  exact lockstep.
* `Turing.OracleTM.queryString_length_le` — in an initialized run, the query after `t`
  steps has length at most `t`.
* `Turing.OracleTM.runFrom_workTapes_blank` — in an initialized run, cells at distance
  `≥ t` are still blank after `t` steps; the certificate that the no-blank fallback in
  `queryString` is unreachable from initialization.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4: oracle machines; Definition 3.4.)
-/

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- An oracle Turing machine with `k` ordinary work tapes, one query tape (the work tape
of index `Fin.last k` in its configurations `Cfg (k + 1)`), and designated query and
answer states. Finiteness of `State` is deferred exactly as for `MultiTapeTM`, and so is
distinctness of the three special states: the raw structure allows them to coincide
(with degenerate behavior, e.g. `qYes = qQuery` re-queries forever after a positive
answer), and the faithful interface imposes `OracleTM.WellFormed`.
[AB09, Definition 3.4] -/
structure OracleTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- entering this state submits the query tape's contents to the oracle -/
  qQuery : State
  /-- the state the oracle answer step moves to on a positive answer -/
  qYes : State
  /-- the state the oracle answer step moves to on a negative answer -/
  qNo : State
  /-- transition function on the `k + 1` work tapes (the last being the query tape);
  consulted in every state except `qQuery` -/
  tr (q : State) (input : Option Symbol) (work : Fin (k + 1) → Option Symbol) :
    Action (k + 1) Symbol State

namespace OracleTM

variable {M : OracleTM k Symbol State}

/-- Well-formedness of an oracle machine: the query state and the two answer states are
pairwise distinct. Without this, the advertised semantics degenerates: with
`qYes = qQuery` a positive answer re-queries the unchanged tape forever (a negative
answer may still reach a distinct `qNo` and halt normally), and with all three states
collapsed the machine loops once the common query state is reached (an initial state
elsewhere can still halt via the table without ever querying). Moreover `qYes = qNo`
alone makes the step function — hence every run — oblivious to the oracle. This is the
standing hypothesis of the faithful oracle interface —
oracle complexity classes will require it. `q₀ = qQuery` is deliberately allowed: such a
machine simply submits the empty query on its first step.
(`audits/phase1-findings.md`, finding 2.) -/
structure WellFormed (M : OracleTM k Symbol State) : Prop where
  /-- the query state is not the positive-answer state -/
  qQuery_ne_qYes : M.qQuery ≠ M.qYes
  /-- the query state is not the negative-answer state -/
  qQuery_ne_qNo : M.qQuery ≠ M.qNo
  /-- the two answer states are distinct -/
  qYes_ne_qNo : M.qYes ≠ M.qNo

/-- The index of the query tape among the `k + 1` work tapes. -/
def queryTapeIdx (k : ℕ) : Fin (k + 1) := Fin.last k

open Classical in
/-- The query string of a configuration: the contents of the query tape from cell `0`
rightward, up to (excluding) the first blank cell. If no blank cell exists on the
nonnegative half-tape — impossible in configurations reachable from an initial
configuration, but possible for an arbitrary one — the query is `[]`. -/
noncomputable def queryString (cfg : Cfg (k + 1) Symbol State input) : List Symbol :=
  if h : ∃ n : ℕ, cfg.workTapes (queryTapeIdx k) (n : ℤ) = none then
    (List.range (Nat.find h)).filterMap fun n => cfg.workTapes (queryTapeIdx k) (n : ℤ)
  else []

open Classical in
/-- One step of the oracle machine `M` relative to the oracle `O`. In state `qQuery` the
machine moves to `qYes` or `qNo` according to whether the current query string is in `O`,
leaving tapes, head positions and output unchanged; in every other state it steps by its
transition function exactly like a plain machine. [AB09, §3.4] -/
noncomputable def step (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) : Cfg (k + 1) Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q =>
    if q = M.qQuery then
      { cfg with state := some (if queryString cfg ∈ O then M.qYes else M.qNo) }
    else
      (M.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The initial configuration of an oracle machine: all `k + 1` work tapes (including the
query tape) blank. -/
@[simp]
def initCfg (M : OracleTM k Symbol State) (input : List Symbol) :
    Cfg (k + 1) Symbol State input :=
  Cfg.init M.q₀ input

/-- The configuration reached by running `M` with oracle `O` for `t` steps from `cfg`. -/
noncomputable def runFrom (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) (t : ℕ) : Cfg (k + 1) Symbol State input :=
  (M.step O)^[t] cfg

/-- `M` with oracle `O` halts on `input` within `t` steps with `output` on its output
tape. Time-only, mirroring `Turing.FinTM.ComputesInTime`. -/
def ComputesInTime (M : OracleTM k Symbol State) (O : Language Symbol)
    (input output : List Symbol) (t : ℕ) : Prop :=
  (M.runFrom O (M.initCfg input) t).state = none ∧
  (M.runFrom O (M.initCfg input) t).output = output

/-- Away from the query state, a step of an oracle machine does not depend on the oracle. -/
theorem step_eq_of_ne_qQuery (O₁ O₂ : Language Symbol)
    {cfg : Cfg (k + 1) Symbol State input} (h : cfg.state ≠ some M.qQuery) :
    M.step O₁ cfg = M.step O₂ cfg := by
  sorry

/-- In an initialized run, the query after `t` steps has length at most `t`. In
particular the no-blank fallback branch of `queryString` is unreachable from an initial
configuration.

**Proof sketch.** By induction on `t`, every write performed in the first `t` steps
happened at a head position of absolute value at most `t - 1` (heads start at `0` and
move at most one cell per step, `Turing.workTapePos_apply_le`). Hence cell `t` of the
query tape is still blank at time `t`, so the least-blank search in `queryString`
terminates at an index `≤ t`. -/
theorem queryString_length_le (M : OracleTM k Symbol State) (O : Language Symbol)
    (x : List Symbol) (t : ℕ) :
    (queryString (M.runFrom O (M.initCfg x) t)).length ≤ t := by
  sorry

/-- In an initialized run, every work-tape cell at distance at least `t` from the
origin is still blank after `t` steps. This is the certificate that the no-blank
fallback branch of `queryString` is unreachable from initialization (the length bound
`queryString_length_le` alone does not certify this, since the fallback also returns a
short list).

**Proof sketch.** Simultaneous induction on `t` with the head-position bound
`|workTapePos i| ≤ t`: at `t = 0` all tapes are blank and heads are at `0`; an ordinary
step writes only at the *old* head position (of absolute value `≤ t`, hence `< t + 1`;
`Action.apply` writes before moving) and moves each head by at most one cell
(`Turing.workTapePos_apply_le`); oracle-answer and halted steps change no tape. -/
theorem runFrom_workTapes_blank (M : OracleTM k Symbol State) (O : Language Symbol)
    (x : List Symbol) (t : ℕ) (i : Fin (k + 1)) (z : ℤ) (hz : (t : ℤ) ≤ |z|) :
    (M.runFrom O (M.initCfg x) t).workTapes i z = none := by
  sorry

end OracleTM

/-- Extend an action on `k` work tapes to `k + 1` work tapes: the extra (last) tape is
neither written nor moved. -/
def Action.extend (a : Action k Symbol State) : Action (k + 1) Symbol State where
  inputTape := a.inputTape
  workTapes := fun i =>
    if h : (i : ℕ) < k then a.workTapes ⟨i, h⟩ else (none, 0)
  output := a.output
  state := a.state

/-- Rename the states of an action along a function. -/
def Action.mapState {State' : Type*} (f : State → State') (a : Action k Symbol State) :
    Action k Symbol State' where
  inputTape := a.inputTape
  workTapes := a.workTapes
  output := a.output
  state := a.state.map f

/-- Embed a `k`-tape configuration into a `k + 1`-tape configuration over the extended
state type `State ⊕ Fin 3`: the extra work tape is blank with its head at `0`, and the
state is renamed along `Sum.inl`. -/
def Cfg.embedOracle (cfg : Cfg k Symbol State input) :
    Cfg (k + 1) Symbol (State ⊕ Fin 3) input where
  state := cfg.state.map Sum.inl
  inputPos := cfg.inputPos
  workTapes := fun i =>
    if h : (i : ℕ) < k then cfg.workTapes ⟨i, h⟩ else fun _ => none
  workTapePos := fun i => if h : (i : ℕ) < k then cfg.workTapePos ⟨i, h⟩ else 0
  output := cfg.output

namespace OracleTM

/-- Embed a plain machine as an oracle machine that never queries: the state type is
extended by three fresh states serving as `qQuery`, `qYes`, `qNo`, and the transition
function acts as before on original states (never moving into the fresh states, and
ignoring the query tape). The fresh states are unreachable from the initial
configuration. The *transition table* halts immediately from all three fresh states;
note that from `qQuery` itself the query override fires first (one answer step into
`qYes`/`qNo`, whose table entries then halt) — the table's `qQuery` row is dead code. -/
def ofMultiTapeTM (tm : MultiTapeTM k Symbol State) : OracleTM k Symbol (State ⊕ Fin 3) where
  q₀ := .inl tm.q₀
  qQuery := .inr 0
  qYes := .inr 1
  qNo := .inr 2
  tr q inp work :=
    match q with
    | .inl q => ((tm.tr q inp fun i => work i.castSucc).mapState Sum.inl).extend
    | .inr _ => ⟨0, fun _ => (none, 0), none, none⟩

/-- The embedding of a plain machine is well-formed: its three fresh special states are
pairwise distinct by construction. -/
theorem ofMultiTapeTM_wellFormed (tm : MultiTapeTM k Symbol State) :
    (ofMultiTapeTM tm).WellFormed := by
  constructor <;> simp [ofMultiTapeTM]

/-- **Sanity check for the oracle architecture** (plan §3.1): an embedded plain machine
runs in lockstep with the original under every oracle.

**Proof sketch.** By induction on `t` it suffices to show that `Cfg.embedOracle`
intertwines the two step functions. In a configuration `Cfg.embedOracle cfg` the state is
of the form `Sum.inl q` (or `none`), which is never `qQuery = Sum.inr 0`, so the oracle
step reduces to applying the extended action; and applying an extended, state-renamed
action to an embedded configuration is the embedding of applying the original action —
the extra tape is untouched (`Action.extend` neither writes nor moves it), and reads
agree because the embedded work tapes restrict to the original ones. -/
theorem runFrom_ofMultiTapeTM (tm : MultiTapeTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    (ofMultiTapeTM tm).runFrom O cfg.embedOracle t = (tm.runFrom cfg t).embedOracle := by
  sorry

/-- An embedded plain machine has the same input/output behavior and time bounds as the
original, relative to every oracle. In particular its behavior is oracle-independent.

**Proof sketch.** `Cfg.embedOracle` sends the initial configuration of `tm` to the initial
configuration of the embedded machine (both have blank work tapes and heads at `0`); by
`runFrom_ofMultiTapeTM` the runs correspond, and `Cfg.embedOracle` preserves haltedness
and the output tape. -/
theorem computesInTime_ofMultiTapeTM (tm : MultiTapeTM k Symbol State) (O : Language Symbol)
    (input output : List Symbol) (t : ℕ) :
    (ofMultiTapeTM tm).ComputesInTime O input output t ↔
      ((tm.runFrom (tm.initCfg input) t).state = none ∧
        (tm.runFrom (tm.initCfg input) t).output = output) := by
  sorry

open Classical in
/-- The converse of `ofMultiTapeTM` for the empty oracle: an oracle machine run with the
empty oracle is eliminated into a plain `k + 1`-tape machine over the *same* state type,
by replacing the query behavior with a stationary transition into `qNo` (the empty
oracle always answers no). (`audits/phase1-findings.md`, finding 8.) -/
noncomputable def plainEmptyOracle (M : OracleTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol State where
  q₀ := M.q₀
  tr q inp work :=
    if q = M.qQuery then ⟨0, fun _ => (none, 0), none, some M.qNo⟩
    else M.tr q inp work

/-- **Sanity check, converse direction**: the empty-oracle elimination runs in exact
lockstep with the oracle machine on the empty oracle — same configurations at every
step, from every starting configuration.

**Proof sketch.** Pointwise on `step`, then induction on `t`. On a halted configuration
both sides are fixed. In state `qQuery` the oracle step answers `qNo` (nothing is in the
empty oracle) and changes only the state; the plain machine applies the stationary
action `⟨0, no writes/moves, no output, some qNo⟩`, whose `Action.apply` moves the input
head by `0` (`Turing.moveInputPos_zero`), leaves every work tape and head unchanged, and
appends nothing — the same configuration. In any other state both sides apply the same
transition-table action. -/
theorem runFrom_plainEmptyOracle (M : OracleTM k Symbol State)
    (cfg : Cfg (k + 1) Symbol State input) (t : ℕ) :
    -- `0` is the empty language (`Language`'s `Zero` instance)
    M.plainEmptyOracle.runFrom cfg t = M.runFrom (0 : Language Symbol) cfg t := by
  sorry

end OracleTM

end Turing
```
