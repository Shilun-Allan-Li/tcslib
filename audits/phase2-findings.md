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
