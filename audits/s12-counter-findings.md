# §12.7 counter-driven loops — statement-gate findings

**Verdict: PASS for the stated surface — 0 blockers, 0 majors, 1 minor, 5 notes.** The gate may close and commission the fill batch. No false theorem or missing soundness hypothesis was found. This verdict does not certify completion of the downstream nondeterministic interpreter or its branch-alignment proof.

**Scope:** the supplied `TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean`, identified by the pack as branch `complexity/arora-barak-ch3-4`, commit `e44b5656`: 12 `def`s, one inductive type, its derived `DecidableEq` and explicit `Fintype` instance, and all 10 sorried theorems. No source changes were made.

**Method:** read the pack; extracted a comment-free copy of CounterLoop; recorded all 23 blind restatements before reading CounterLoop's docstrings; then compared with the design, supporting definitions, harness, and four consumer attachments. The pack necessarily disclosed intended behavior before the blind pass; the declaration docstrings did not. This is a statement audit with mathematical derivations and independent executable checks, **not a Lean proof completion**.

## Findings table

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| SC-1 | minor | `Build/CounterLoop.lean:240–244` · `counterOverhead` docstring | “The exact cost of the first `r` decrements” needs its physical-execution range stated. | `counterWord` freezes at zero, whereas the machine wraps on underflow. For `w = [true]`, `counterOverhead w 3 = 2 + 4 + 4 = 10`; three restarted physical decrements cost `2 + 4 + 2 = 8`. The loop exits on its first underflow, so every theorem's use is within the correct range. | Say that the expression is the cost sum for the frozen word orbit, and coincides with the physical countdown through at most its first underflow (`r ≤ value + 1`). No theorem change. |
| SC-2 | note | `counterWord_value`; both host theorems · `hround` | Several hypotheses are redundant, harmlessly. | `counterWord_value` remains true for every natural `r`, using truncated subtraction. Live endpoints imply interior liveness. All escape-round positivity follows from eventual arrival at `e ≠ a`. In the returning theorem, later starts duplicate earlier returns. Details and deletion counterexamples appear below. | No change required. Record the redundancies; do not mistake the returning theorem's positivity or either theorem's interior anchor avoidance for redundant conditions. |
| SC-3 | note | `counterLoopTM`; `Diagonalization/NTimeHierarchy.lean:121` · `exists_timed_universal_NDTM` | The arithmetic meets the linear-clock requirement; the supplied host contracts are deterministic. | Their parameter is `MultiTapeTM` and their orbit is `runFrom`. There is no choice stream, `NDTM.runWith`, or all-branch quantifier. The consumer explicitly requires passing choice bits through and proving both alignment directions. | Before that consumer's fill, provide or cite an ND/choice-stream lifting contract with alignment through bookkeeping pauses. This is additional consumer work, not a refutation of these deterministic statements. |
| SC-4 | note | `Build/Seam.lean:176` · private `seamComp_left`; design decision 12.7.2 | Both exits can be wired correctly, but two invocations of the public endpoint theorem alone do not express every branch of the nested construction. | If the inner seam attaches the `done` continuation, the escape path never reaches that seam's designated exit, so `seamCompTM_run_ofCfg`'s `hexit` cannot establish its pre-dispatch prefix. The needed prefix correspondence is already proved as private `seamComp_left`. | Expose the existing prefix lemma, or cite an adequate shared transport interface, when assembling the two-continuation consumer. Do not copy its induction. No CounterLoop statement change is needed. |
| SC-5 | note | Both host theorems · trajectory clauses | The clauses suffice for space accounting, including mid-decrement times. | They imply that each body's visited set is contained in the corresponding single concatenated body run; the extra tape visits at most `w.length + 2` cells. Live exits are stationary, so the bounds persist after completion. | A public visited-set / `spaceUsedByTape` corollary would prevent repeated bookkeeping, but is not needed to make the current statements true or usable. |
| SC-6 | note | Pack · verification and duplication attestations | Distinguish packet evidence, independent checks, and repository-wide certification. | The supplied Lean harness compares bounded cell samples; the supplied results are a summary, not raw compilation/lint logs. The independent model below compares entire represented infinite tapes. This audit did not rerun Lean or lint, verify the git commit object, or recalculate an unattached repository-wide duplication ledger. | Retain the reported results as author evidence; run the required checker and lint at the fill gate. Do not describe this audit as a fresh kernel check or a repository-wide duplication clearance. |

## Blind restatements and comparison: 13 definitions

Each row was recorded from the comment-free declarations. Source line numbers below refer to the extracted Lean attachment.

| Definition | Literal restatement | Comparison with §12.7 and docstring |
|---|---|---|
| `Action.mapWorkSymbols` (101) | Apply the equivalence to symbols in requested work-tape writes. Preserve both no-write and write-blank cases, all movements, output, and next state. | Matches symbol transport. The two nested `Option.map`s are necessary because no write differs from erasing a cell. |
| `Cfg.mapWorkSymbols` (110) | Map every nonblank work cell; preserve blanks, state, all positions, and output. | Matches. Input symbols and emitted output are deliberately not renamed. |
| `MultiTapeTM.mapWorkSymbols` (117) | Keep the initial state. Decode scanned work symbols with the inverse equivalence, consult the original table, then encode work writes with the equivalence. | Correct conjugation. An arbitrary equivalence suffices; involutivity is unnecessary. |
| `decFixed` (145) | Little-endian borrow: empty fails; a leading true becomes false; a leading false becomes true precisely when recursive decrement of the tail succeeds. | Matches fixed-width predecessor with explicit underflow. On failure it returns no word, not the machine's wrapped word. |
| `decrementTM` (160) | Conjugate the existing `incrementTM` by Boolean negation on work symbols. | Matches decision 12.7.4. There is no decrement transition-table copy. State verdicts are not complemented. |
| `counterWord` (237) | Iterate the predecessor operation, retaining the current word whenever it underflows. | Matches its explicit freeze-at-zero docstring. Distinct from physical wrapping after underflow. |
| `counterOverhead` (243) | For each index below `r`, charge twice the initial-false prefix length of `counterWord w j`, plus two. | Correct cost through the first underflow; unrestricted physical wording is SC-1. |
| `CounterLoopState` (298), instances (307–310) | A disjoint body-state copy, a decrement-phase copy, and two additional live exits. Decidable equality and finiteness are inherited as appropriate. | Correct: the state count for finite `S` is `Fintype.card S + 7` (five `FlagPhase` states and two exits). No finiteness assumption is needed for the generic `MultiTapeTM` statements. |
| `counterLoopRedirect` (315) | A target equal to `a` enters decrement; otherwise a target matching the optional exit escapes; otherwise retain the body state. | Correct, with **anchor priority** when `exit = some a`. |
| `counterLoopDecExit` (322) | Success enters `body a`; underflow enters `done`; other decrement phases remain decrement phases. | Matches. It rewrites a transition's target, without adding a transition. |
| `counterLoopTM` (335) | Start in decrement. Run the body on the first `k` tapes or decrement on the last tape, redirecting successor states in place. Both exits have stationary, silent, write-free self-loops. | Matches all six design decisions. A source halt remains a physical halt; it is not silently converted to `escape`. The round hypotheses exclude that case. |
| `counterLoopCfg` (352) | Embed body tapes and heads, retain its input position and output, install the extra counter tape/head, and overwrite the state with the supplied host state. | Matches. `c.state` is genuinely ignored, and prefix `[]` gives exactly `c.output`, not an empty output. |
| `counterLoopOrbit` (361) | Iterate the configuration-dependent operation `c ↦ M.runFrom c (τ c)`. | Matches. It does not reset tapes, heads, input position, or output between rounds. |

The design's initial shorthand `S ⊕ FlagPhase` is refined by the concrete inductive type to include the two requested live exits. The orbit formulation removes the need to quantify an invariant `P`; a consumer can derive the orbit hypotheses from its own invariant. These are faithful refinements.

## Blind restatements and truth arguments: 10 theorems

For brevity, write `c_r = counterLoopOrbit M τ c r`. This is only notation in this report.

1. **`MultiTapeTM.mapWorkSymbols_runFrom` (130).** At every natural time, running the conjugated machine from the conjugated configuration equals conjugating the original run. In one step, inverse decoding recovers precisely the original reads, and postcomposing cell values commutes with each requested cell update; blank erasure, no-write, heads, input movement and output also agree. The halted case is the identity, and induction on time gives the displayed equality for arbitrary configurations and equivalences.

2. **`decrementTM_run_succ_ofCfg` (177).** From state `run` with a buffered word and both delimiters at the displaced head, successful decrement reaches `done true` at exactly `2q + 2`, changes only the word interval to the predecessor, restores all heads, and preserves input position/output. Neither verdict appears earlier; the selected head remains in `[pos−1, pos+q]` and all other heads stay fixed. Complementing the configuration and word converts every premise and conclusion to `incrementTM_run_succ_ofCfg`, including the exact prefix length and the arbitrary outer frame.

3. **`decrementTM_run_underflow_ofCfg` (211).** With the same framed premises and a zero word, after exactly `2|w| + 2` steps only the word interval has become all true and the state is `done false`. There is no earlier verdict, the selected head stays in `[pos−1, pos+|w|]`, and every other field is preserved. Complementation gives the increment-overflow theorem; the empty-word run still takes two steps and visits the left delimiter.

4. **`counterWord_length` (250).** Every number of frozen-at-zero decrements preserves the original width. List induction shows successful `decFixed` preserves length, and the failure branch keeps the original word. Iteration preserves this property, including all times after reaching zero.

5. **`counterWord_value` (261).** For `r` at most the original little-endian binary value, the new value is the original minus `r`. A positive word splits into a false prefix followed by a true bit; its predecessor changes the weighted value by exactly one, and zero is precisely the all-false word. Induction proves the claim; because zero freezes, the same equality with natural truncated subtraction also holds without `hr`.

6. **`counterOverhead_le_of_le` (276).** Through any successful prefix of `r` decrements, the cost is at most `4r + 2|w|`. The number of true bits supplies a telescoping potential, proved below. Noncanonical high false bits do not invalidate the estimate, and `r = 0` needs no separate positivity assumption.

7. **`counterOverhead_le` (289).** Counting all `d` successful decrements and the subsequent underflow costs at most `4d + 2|w| + 2`. The successful part costs exactly `4d − 2·ones(w)`; the final zero word has the original width and costs `2|w| + 2` to underflow. This includes equality in the upper bound when `d = 0`.

8. **`counterLoopTM_run_done` (389).** If all `d` orbit rounds start at `a`, have positive exact duration, avoid halting/anchor/exit internally, and return to `a`, the host first reaches `done` at the sum of those durations and `counterOverhead w (d+1)`. Its body data are exactly `c_d`, the counter interval is all true, its counter head is restored, and the stated whole-trajectory bounds hold. Induct over rounds using framed decrement and body embedding; redirecting the final transition changes only its successor state. For `d = 0`, the round premises are empty and the body part remains `c` for **every** `c.state`.

9. **`counterLoopTM_run_escape` (438).** If rounds through `r₀` start at `a`, avoid both anchors internally, and the last ends at distinct `e`, with `r₀ < d`, the host first reaches `escape` after `r₀+1` body rounds and exactly that many successful decrements. Earlier rounds return to `a` because their endpoints are the next round starts in `hround`; no extra return premise is missing. The final body data equal `c_(r₀+1)`, the counter is `counterWord w (r₀+1)`, and its head is restored with the stated trajectory bounds. The strict budget condition includes escape on the last permitted round, before any underflow.

10. **`counterLoop_time_le` (481).** A bound `B` on each of the first `d` orbit costs bounds their sum plus the complete decrement overhead by `dB + 4d + 2|w| + 2`. Sum the `d` inequalities and apply the whole-run arithmetic bound. It is intentionally an arithmetic corollary: actual host behavior additionally requires the host theorem's premises, while this inequality needs neither a start-state condition nor `B > 0`.

## Adversarial instantiations — question 1

In this table, Boolean words are written with `0 = false`, `1 = true`, in **little-endian order**. Each row contains at least three concrete boundary instantiations. Checks include every asserted conclusion appropriate to that instance, not merely its final state.

| Theorem | Instantiation A | Instantiation B | Instantiation C / additional attack | Outcome |
|---|---|---|---|---|
| Symbol transport | `t = 0`, arbitrary nonempty output and work frame. | Already halted configuration, nontrivial equivalence and negative work heads, times through 8. | Three-symbol cycle `0→1→2→0`, including blank writes, no-writes, input movement and unchanged emitted symbols; also `k = 0`. | All hold. The three-cycle specifically tests an equivalence that is not an involution. |
| Decrement success | `w=[1]`, `q=0`, `cp=-4`: `[0]` at time 2, head interval `[-5,-4]`. | `w=[0,0,1]`, `q=w.length−1=2`, `cp=3`: `[1,1,0]` at time 6. | `w=[1,0,0]`, `q=0`, active tape 1 and the other head displaced: high zero padding retained, time 2. | All hold, including unchanged outer cells, other tape, input and output. |
| Decrement underflow | `w=[]`, `cp=-4`: time 2, path `-4,-5,-4`, no cell write. | `w=[0]`: `[1]` at time 4. | `w=[0,0,0]`, `cp=3`: `[1,1,1]` at time 8; path contained in `[2,6]`. | All hold. A blank word does not mean zero transitions. |
| Word length | `w=[]`, `r=3`: length 0. | `w=[0,0]`, `r=5`: unchanged zero word, length 2. | `w=[0,0,1]`, `r=6`: frozen `[0,0,0]`, length 3. | All hold past underflow as well as before it. |
| Word value | `w=[]`, `r=0`: `0=0`. | `w=[0,0,1]`, `r=1`: `[1,1,0]`, value `3=4−1`. | `w=[1,0,0]`, `r=1`: value 0; additionally `r=3` still gives `0=max(1−3,0)`. | All hold; the additional out-of-range test illustrates redundancy of `hr`. |
| Prefix overhead | `w=[]`, `r=0`: `0≤0`. | `w=[0,0,1]`, `r=1`: `6≤4+6=10`. | `w=[1,1,1]`, `r=7`: costs `2+4+2+6+2+4+2=22≤28+6=34`. | All hold. Deleting `hr` is unsafe: `w=[0,0]`, `r=3` gives `18>16`. |
| Whole overhead | `w=[]`: `2=2`. | `w=[0,0]`: `6=6`. | `w=[0,0,1]`: `6+2+4+2+8=22≤16+6+2=24`; also `w=[1,1,1]`: `30≤36`. | All hold, with the advertised zero-value equality. |
| Returning host | `w=[]`, `c.state=none`: time 2, exact body data `c`; repeated with unrelated live state. | `w=[0,0]`, `cp=-6`, displaced body heads, arbitrary `c.state`: time 6 and all-true counter. | `w=[1]`, one-step emitting/input-moving body, `exit=some a`: time 7; anchor priority prevents escape. Also grow-body value 5, `exit=none`, round costs `3,4,6,8,10`: time `31+24=55`. | All hold; the two zero cases have genuinely vacuous round hypotheses. |
| Escaping host | `w=[1]`, `r₀=0`, one-step body `a→e`, moving heads/input and emitting: escape at time 3, zero counter. | `w=[1,1]`, body marks blank→false→true then exits, `r₀=2=d−1`: time `3+(2+4+2)=11`, counter `[0,0]`. | Same third-round escape with `w=[1,0,1]`, `cp=-6`, body heads `(-3,4)`: time `3+(2+6+2)=13`, counter `[0,1,0]` of value 2. | All hold. Negative counter/body coordinates, last-round escape, and arbitrary frames cause no mismatch. |
| Uniform bound | `d=0`, `w=[]`, `B=0`: `2≤2` with no round restrictions. | `w=[1]`, one-step rounds, `B=1`: `7≤1+4+2+2=9`. | `w=[1,0,1]`, grow-body `B=10`: `55≤50+20+6+2=78`; also a zero-cost abstract orbit with positive `d`, `B=0`, satisfies this arithmetic statement. | All hold. Removing `hB` can fail: `d=1`, `w.length=1`, `τ=3`, `B=0` gives `9>8`. |

The independent model covered all 511 Boolean words of width at most 8 for arithmetic, all 63 words of width at most 5 at three head placements and both selected tape indices for decrement, and the host families above across small counters. Detailed counts are recorded under evidence below.

## Necessity, sufficiency, and redundancies — question 2

In the counterexamples below, unspecified transitions are stationary live self-loops, unspecified tape actions are idle, and the counter is correctly framed. Distinct state names denote distinct states. Thus these examples delete the indicated condition, not the delimiter or time-definition premises at the same time.

| Condition | Necessity or redundancy |
|---|---|
| Returning `hround`: start at `a` | The initial start condition is necessary when `d>0`. Set `d=1`, `τ=1`, initial body state `b≠a`, with `b→a` emitting false and `a→a` emitting true. The abstract round and host finish with different outputs, since the host enters `body a` regardless of `c.state`. For `r>0`, the start condition follows from the preceding round's return condition. |
| Returning `hround`: `0<τ(c_r)` | Necessary. With `w=[1]`, `τ=0`, and stationary `a→a`, all other premises hold, but the formula gives `T=6`; the host requires a real body step and first reaches done at 7. |
| Returning `hround`: intermediate state is live | Redundant given the live endpoint. If a round halts internally, halting absorption makes its endpoint halted, contradicting its return to `a`. This concerns the liveness component of the existential; deleting the entire existential would also delete its necessary avoidance conditions. |
| Returning `hround`: no intermediate `a` | Necessary. With `w=[1]`, stationary `a→a`, and `τ=2`, the formula gives 8, but the host first reaches done at 7. Its final configuration at 8 is not enough: the no-earlier-exit conclusion fails. |
| Returning `hround`: no intermediate optional exit | Necessary in general. With distinct `e`, `exit=some e`, `a→e→a`, `τ=2`, and `w=[1]`, the abstract round returns, but the host escapes at 3 instead of completing the claimed returning run at 8. For `exit=none` this condition is tautological; for `exit=some a` it duplicates anchor avoidance. |
| Returning `hround`: final state `a` | The last return is necessary. With `d=1`, `τ=1`, and `a→b≠a`, the host remains in its body rather than starting the final decrement. Earlier returns duplicate the next round's start assertion. For `d=0`, neither start nor return constraints are needed. |
| Escaping `hround`: each start at `a` | Necessary. The initial-state output counterexample above works with `b→e` and `a→e`. Later starts also matter: with `w=[0,1]`, `r₀=1`, `τ=1`, and `a→b→e`, deleting the round-1 start condition invents a second decrement that the physical run never performs; the host escapes with value 1 instead of 0. |
| Escaping `hround`: positive durations | **Redundant for every round**, not just the last. If `τ(c_r)=0`, then `c_(r+1)=c_r`; iteration of the same configuration-dependent map gives `c_(r+j)=c_r` for every `j`. Its state is `a`, contradicting `c_(r₀+1).state=some e` and `e≠a`. |
| Escaping `hround`: intermediate liveness | Redundant. Earlier endpoints are `a` by the next-start premise; the last endpoint is `e` by `hexit`. Absorption of halt rules out a halted intermediate state in either case. |
| Escaping `hround`: no intermediate `a` | Necessary. Let a one-tape body at `a` write false on its initially blank current cell and return to `a`; when it reads that false, let it enter `e`. With `τ=2`, `r₀=0`, `w=[1]`, the abstract endpoint is `e`, but the host decrements again after the first body step and times out instead. The claimed escape time is 4; it actually reaches done at 7. |
| Escaping `hround`: no intermediate `e` | Necessary. Take `a→e→e`, `τ=2`, `r₀=0`, `w=[1]`. The formula gives 4, but the host first escapes at 3, violating the cut. |
| Escape `hea : e≠a` | Necessary. With `e=a`, stationary one-step `a→a`, `w=[1]`, `r₀=0`, all remaining premises hold. At the claimed escape time 3 the host is `dec run`, because anchor redirection has priority. |
| Escape `hr₀ : r₀<d` | Necessary. With `w=[]`, `r₀=0`, and one-step `a→e`, the remaining premises hold, but the host reaches done at 2 without running the body; it is not escape at the formula's time 3. |
| Escape `hexit` | Necessary. With one-step `a→a`, `w=[1]`, `r₀=0`, the interior is empty and all other premises hold, but the host re-enters decrement rather than escaping. |

The liveness argument can be written directly as follows, for an internal time `u < τ(c_r)`:

\[
M.\mathrm{runFrom}(c_r,\tau(c_r))
=M.\mathrm{runFrom}\bigl(M.\mathrm{runFrom}(c_r,u),\tau(c_r)-u\bigr).
\]

If the inner configuration has state `none`, the right side is that same halted configuration. Both theorems require a live endpoint, a contradiction.

Other premise checks:

- The round cuts properly exclude time zero. A body launched at `a` must execute `a`'s action once; the host redirects **arrivals**, not the current state before that action.
- The two delimiter hypotheses suffice even with arbitrary infinite nonblank outer frames. Removing the left blank can let rewind continue past the original head; removing the right blank can turn an intended underflow into success. In the success theorem the right delimiter is stronger than necessary, since the first true bit is reached earlier, but retaining the common framed interface is harmless.
- `hv` and the initial decrement state matter: `[0]` cannot satisfy the success verdict, `[1]` cannot satisfy underflow, and an initially completed decrement state violates the no-earlier-verdict clause at time zero.
- No assumption that the body leaves the counter alone is missing: its transition only receives the selected first `k` work symbols, and `embedEmitTM` leaves the last tape/head unchanged.
- No finiteness or computability assumption on `τ` is missing. It is an analysis function, not information consulted by the host. A finite-state wrapper requires a finite body state type; the provided instance supplies the host's finiteness.
- `counterWord_value.hr` is redundant because natural subtraction saturates at zero. The prefix-overhead restriction is not redundant, as the `18>16` example demonstrates. A uniform whole-loop `B>0` hypothesis is unnecessary.

## Exact time and final configurations — questions 3 and 4

For a successful decrement with `q` initial false bits, its phases cost:

\[
\underbrace{q}_{\text{borrow right}}
+\underbrace{1}_{\text{flip true, move left}}
+\underbrace{q}_{\text{rewind left}}
+\underbrace{1}_{\text{left blank, move right}}
=2q+2.
\]

For underflow, replace `q` by `|w|`; the turn occurs at the right blank and writes nothing there. Consequently the head returns to its original coordinate even at width zero. Every cell write lies strictly inside the original word interval.

Immediately before decrement number `r`, the host's elapsed time and data are

\[
\sum_{j<r}\tau(c_j)+\operatorname{counterOverhead}(w,r),
\qquad \text{body data }c_r,\quad
\text{counter word }\operatorname{counterWord}(w,r),\quad
\text{counter head }cp.
\]

The successful decrement's **last transition** has target `body a`; the body round's **last transition** has target `dec run` or `escape`. `Action.mapState` preserves that same transition's writes, movements and emission. There is no extra dispatch transition at either seam.

Thus the returning time is exactly

\[
\sum_{r<d}\tau(c_r)+\operatorname{counterOverhead}(w,d+1),
\]

with one decrement before each of the `d` rounds and one final underflow. The last zero word has length `|w|`; underflow turns its interval into all true, preserves every exterior counter cell, and restores the head to `cp`. Body tapes, body heads, input position, and accumulated output are exactly those of `c_d`.

For escape, exactly `r₀+1` successful decrements precede exactly `r₀+1` rounds:

\[
\sum_{r<r_0+1}\tau(c_r)+\operatorname{counterOverhead}(w,r_0+1).
\]

There is no trailing underflow. The counter is `counterWord w (r₀+1)`, including the all-false word when `r₀=d−1`. The body's final transition, including any output on that transition, is retained. Since `embedEmitCfg` uses prefix `[]`, the output is the orbit's complete output, including its initial prefix; it is neither reset nor duplicated.

The intermediate cuts exclude body exits, and the decrement contracts exclude both verdicts before their last step. These facts establish the whole host's first-exit clauses, not just equality after an exit's stationary self-loop.

## Trajectories and space — question 5

The quantifier order is correct: one pair `r,u` works simultaneously for **all** body heads at a host time. During the decrement before round `r`, choose `u=0` and body configuration `c_r`; during its body phase choose the corresponding local body time. During the final underflow choose `r=d,u=0`. At escape use the last body's endpoint, which is explicitly allowed.

Repeated use of `runFrom_add` gives

\[
c_r=M.\mathrm{runFrom}\left(c,\sum_{j<r}\tau(c_j)\right),
\]

so the returning trajectory clause implies, for each body tape `j`,

\[
\begin{aligned}
&\operatorname{visitedByTapeHead}_{\text{host}}
  (\text{start},T,j.\mathrm{castSucc})\\
&\qquad\subseteq
 M.\operatorname{visitedByTapeHead}
 \left(c,\sum_{r<d}\tau(c_r),j\right),\\
&\operatorname{spaceUsedByTape}_{\text{host}}
  (\text{start},T,\mathrm{Fin.last}\ k)\le |w|+2.
\end{aligned}
\]

The escape version replaces `d` by `r₀+1`. Taking cardinalities gives the useful per-body-tape space bound; summing gives the body run's total space plus `|w|+2`. This uses the union/concatenated run of the body trajectories, **not** the maximum of unrelated per-round cardinalities: drifting rounds may visit disjoint regions.

The interval `[cp−1,cp+|w|]` has exactly `|w|+2` integer positions, also when `cp<0`. Both terminal host states are stationary, so after `T` no new cell is visited. A public corollary expressing these consequences would be useful but is not an additional soundness assumption.

## Amortized bounds — question 6

Let `ones(w)` count the true bits of `w`. For a successful decrement with `q` initial false bits and result `v`, the list shapes are

\[
w=\mathrm{false}^{q}\mathbin{++}(\mathrm{true}::\mathrm{rest}),
\qquad
v=\mathrm{true}^{q}\mathbin{++}(\mathrm{false}::\mathrm{rest}).
\]

Hence, entirely in natural-number arithmetic,

\[
\operatorname{ones}(v)+1=\operatorname{ones}(w)+q,
\qquad
(2q+2)+2\operatorname{ones}(w)=4+2\operatorname{ones}(v).
\]

Summing this identity over `r≤d` successful decrements cancels the intermediate bit counts:

\[
\operatorname{counterOverhead}(w,r)+2\operatorname{ones}(w)
=4r+2\operatorname{ones}(\operatorname{counterWord}(w,r)).
\]

Width preservation and `ones(u)≤|u|` now give

\[
\operatorname{counterOverhead}(w,r)
\le 4r+2\operatorname{ones}(\operatorname{counterWord}(w,r))
\le4r+2|w|.
\]

At `r=d`, the remaining word is all false, so adding its underflow cost yields the stronger exact identity

\[
\operatorname{counterOverhead}(w,d+1)+2\operatorname{ones}(w)
=4d+2|w|+2.
\]

Dropping its nonnegative bit-count term proves the whole-run bound. For positive prefixes the docstring's stronger slack of four is also correct: `ones(w)≥1` and `d−r<2^{|w|}−1` imply the result has at most `|w|−1` true bits. This proves the claimed sharper bound without Legendre or Kummer; those sketches are not concealing a false estimate.

Finally,

\[
\sum_{r<d}\tau(c_r)\le\sum_{r<d}B=dB
\]

gives `counterLoop_time_le` exactly as stated. For an escaping run with the analogous bound through `r₀`, the existing prefix theorem gives

\[
T\le(r_0+1)B+4(r_0+1)+2|w|.
\]

An explicit escape-time corollary is convenient but not missing mathematically. The `2|w|` term must be retained for arbitrary padded counters: a wide all-false counter takes a full underflow sweep even though its value is zero.

## Symbol transport and framed decrement — question 7

The defining read is `e.symm` applied only to nonblank work symbols. On a renamed configuration it cancels `e`; the native input read is unchanged. The work-write operation is transported at both `Option` levels, so a no-write remains no-write, a blank write remains a blank write, and a symbol write is renamed. Output is deliberately unchanged, even when its value equals a symbol being permuted on a work tape.

For Boolean complement, list induction gives

```lean
decFixed w = (incFixed (w.map not)).map (List.map not)
```

and complement twice is the identity on every work cell, including the arbitrary frame. Buffered words commute with this map, including both blank delimiters. The true-prefix count of `w.map not` is exactly the false-prefix count of `w`. The two framed increment statements in the attachment are proved declarations, with exactly the corresponding equality, cut and head-bound clauses.

Consequently both decrement contracts are exact transports of those contracts. No assumption about input position, prior output, nonselected tape contents, head sign, or finite tape support has been smuggled in. Their success/underflow flags remain true/false respectively, since the equivalence acts on work symbols rather than control states.

## Consumer fitness and composition — question 8

| Consumer | What the contracts supply | Remaining consumer obligations / interface detail |
|---|---|---|
| `Codes2Tape.exists_uniformMachineCode2` | A tape-content deadline, persistent source tapes, configuration-dependent exact round cost, zero-round timeout, and escape after inspecting the last allowed source transition. | Build one fixed finite interpreter, not a host instantiated separately for each decoded machine. Prove the binary guard and parser, finite output summary, per-round simulation invariant, and one joint polynomial. A simulated halt must become a live body exit; letting the physical body halt does not satisfy these contracts. |
| EXPCOM uniform simulator | The same deterministic countdown and exit discipline; the whole-run or escape estimate can be combined with a polynomial bound on interpreter rounds. | The counter host does not itself provide a uniform parser or a joint polynomial in code, input and deadline. Those are the attached consumer's separate obligations. |
| NTIME hierarchy | Successful ticks plus one underflow have total at most `4d+2w.length+2`; prefixes have the required one-width additive allowance. With canonical binary budgets, the width term fits a linear budget. | For an ND body, branch-dependent simulation and choice alignment still require a public lifting theorem or ND host contract (SC-3). No deterministic orbit theorem implies all-branch halting or the acceptance equivalence by itself. Bound the remaining round cost by a per-code constant and pay startup and outer halt separately. |
| Space hierarchy | A configuration-count clock stored in binary; at most `w.length+2` visited counter cells and no extra body-head motion. The visited-set consequence above supports constant-factor space bookkeeping. | Prove the clock-width bound, simulated interval checks including the last configuration, and probe/replay. The probe must suppress/discard output into finite control; this host forwards emissions and cannot retract output after a later rejection. No full emitted-word buffer is warranted. |

For one selected continuation, the final equality, live final state, and corresponding no-earlier-exit conjunct instantiate `seamCompTM_run_ofCfg` directly, on the arbitrary configuration. That external seam adds **one** stationary dispatch step, in addition to the host's internal exact time.

Both continuations can be wired by first attaching the done continuation, then attaching the escape continuation at the left-tagged escape state of the first composite. Only the reached continuation dispatches; the other remains in a disjoint state summand. The escape path through the first composite needs a pre-dispatch prefix correspondence; `seamComp_left` proves precisely that but is private in the attachment (SC-4). On the done path the outer escape state stays unreachable, including while the done continuation runs in its disjoint summand. Thus there is no semantic two-exit conflict, but the reusable public proof interface should expose the existing prefix fact rather than require a copied induction.

A `FinTM` wrapper is ordinary record packaging once the body is finite, using the supplied host-state instance. Canonical start configurations are specializations of the framed contract; neither a new finite-machine theorem nor a canonical specialization is necessary to repair this statement surface. No distinctness premise for `exit` is needed in the returning theorem, and no separate no-escape theorem is needed for the instance `exit=none`.

## Duplication — question 9

The new file has **24 explicit declarations** when the explicit `counterLoopStateFintype` instance is counted separately: 12 definitions, one inductive type, one instance, and ten theorem declarations. Its `DecidableEq` implementation is generated. All ten theorem bodies are currently `sorry`; this audit cannot certify the future fill's proof-sharing behavior.

The in-packet comparison found no new wholesale copied table or proved development:

- `decrementTM` is one call to symbol conjugation of the existing increment machine, not a renamed copy of `f2_loopDebitTM`'s table.
- `counterLoopTM` cites `embedEmitTM` for body tape selection and `decrementTM` for the clock. Its four-way control dispatch is the new persistent-bank construction, not the older canonical loop/fuel/replay controller.
- `counterLoopCfg` cites `embedEmitCfg` and `Cfg.mapState` rather than reproducing their tape-selection construction.
- Symbol transport maps work cells and work writes; the attached `StateRenaming` maps control states. Their common record-update pattern is not an existing interchangeable theorem.
- `decFixed` has the expected short borrow recursion, semantically related to private `f2_loopDebit`, but changes its result to `Option` and leaves physical wrapping to the machine. It is the commissioned public word interface, not an undisclosed copied private proof family. The old clock's value/length proofs are not copied into this statement skeleton.
- `counterWord` iterates the new option-valued decrement with freezing; the private catalog clock iterates the wrapped first projection. These agree over the successful prefix, not at arbitrary times after exhaustion.
- The value is Mathlib's inline `Nat.ofDigits` expression; no replacement `loopValue`/`bitsVal` definition was added.

The design explicitly schedules the old private clocks for re-derivation under 12.2c item 12. That recognized retirement work remains; creating this shared target does not itself retire those copies. `Loop.lean`, `Universal.lean`, the full standing duplication ledger, and `Adder.lean` are not attached, so no repository-wide census or independent verification of their current byte contents is claimed. The new decrement proofs should remain transports, and the host proof should cite the embedding/decrement interfaces rather than copy a prior clock development.

## Evidence and verification limits

The uploaded packet SHA-256 is

```text
b94d9648b0cea831fb91b2ee17155e0a4e88f08661dc9504d43fd2d71a360b5a
```

The extracted `CounterLoop.lean` SHA-256, with one terminal newline, is

```text
4ee675ff8b47460451c8fdea71aabfb318e19b3e5ed1477c59e0786fe256ff5a
```

The source inventory matches 13 definitions in the pack's convention and 10 `sorry` bodies. The attached increment framed contracts have actual proof bodies; the older B3 report's description of those contracts as still admitted is historical and was not substituted for the current attached Catalog.

The supplied `CounterLoopPreShip.lean.txt` was inspected against `results.txt`. Its `eq2` compares 40 positions per tape, and `eq3` compares 50; these are executable samples, not literal function equality on all integers. The harness explicitly covers values 0–5 with the grow body and 3,4,5,7 with the escape body; it does not test every value through 7 for every fixture. Its four negative controls are correctly targeted: unrenamed transport input, decrement one step early, host one step early, and the escape counter one decrement short.

An independent Python model was implemented from the attached `Action.apply`, `step`, increment table, symbol transport and host dispatch definitions. Its tapes use periodic defaults with finite overrides, allowing exact equality at **all integer coordinates** for these fixtures; it does not use a sampled-cell equality. This model is independent executable evidence, not a translation certified by Lean.

| Check | Executed count / coverage | Result |
|---|---|---|
| Symbol transport | 18 machine/configuration/equivalence cases, each at times 0 through 8; zero/one/two tapes, halted states, identity/swap/three-cycle permutations | Pass |
| Framed decrement | 342 success and 36 underflow cases; every word of width ≤5, three displaced head pairs, both active tape indices | Pass |
| Word length and saturated value | 45,479 word/iteration pairs each, widths ≤8, iterations through value+3 | Pass |
| Prefix cost bound and exact bit-count identity | 43,946 word/prefix pairs, widths ≤8 | Pass |
| Whole-run cost bound and exact bit-count identity | All 511 words of width ≤8 | Pass |
| Returning host and uniform arithmetic bound | 852 cases; zero/two body tapes, `exit=none` and `exit=some a`, arbitrary body states for value zero, and variable-duration grow body | Pass |
| Escaping host | 354 cases; immediate emitting/input-moving exits and third-round exits including the last allowed round | Pass |
| Full host trajectories | 47,796 time points across the 1,206 host runs; all final fields, both first-exit cuts, head bounds, common body-head witnesses, and terminal stationarity | Pass |
| Width-8 minimum slack | Positive-prefix bound: 4; whole-run bound: 0 | Matches the supplied arithmetic results |

Targeted hypothesis-deletion runs independently confirmed the output mismatch from dropping the initial anchor, the returning zero-duration failure, the early-anchor/early-exit failures, the missing final return, and the failures on dropping `hea` or `hr₀`. These are counterexamples to weakened variants, not to the submitted statements.

No `lake build`, Lean compilation, or repository mutation was performed. The pack's elaboration and `0 FAIL` lint attestations are not contradicted by this review, but were not independently rerun. Suggested fill-gate sanity lemmas are the complement identity, the exact bit-count cost identity, zero-counter completion for arbitrary `c.state`, one-step round completion with `exit=some a`, last-round escape, visited-set containment, and stationarity of both live exits.

## Notation glossary

- `c_r`: `counterLoopOrbit M τ c r`; `τ(c_r)` is that round's stated exact duration.
- `ones(w)`: number of true bits in the Boolean word `w`.
- `0/1` in word examples: false/true, with the least significant bit first; `|w|` is `w.length`.
- `d`: the source statement's `Nat.ofDigits 2 (w.map Bool.toNat)`; “value” means this same expression.
- `q`: initial false-prefix length for a successful decrement; `cp`: initial counter-head coordinate; `r₀`: zero-based exiting round.
- `a,e,b`: body anchor, designated distinct exit, and an auxiliary distinct state used in counterexamples; `T,B`: total host time and uniform round-time bound, as in the source.
- Subscript “host” and `start` in the space display refer to the theorem's `counterLoopTM` and its displayed initial `counterLoopCfg`. No corresponding Lean definitions are proposed.
