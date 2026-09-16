Round 2 external statement audit — Arora–Barak Chapter 1

Audited snapshot: [3a45aa2fb1c88cb2cc70aae19391b328c6238f4b](https://github.com/Shilun-Allan-Li/tcslib/tree/3a45aa2fb1c88cb2cc70aae19391b328c6238f4b), on `complexity/arora-barak-ch1`. All eight attached Lean sources match that snapshot's Git blob hashes. The eight inherited `sorry` statements match [round 1's pinned source](https://github.com/Shilun-Allan-Li/tcslib/tree/65a3fe52774bd3ada3f66fd1509dcd1bbf7a6bc8) exactly, including their hypotheses.

This is a mathematical audit of definitions, statements, and proof sketches. I did not audit tactic scripts or independently rerun Lean; the bundle's elaboration claim is not independently certified here. The requested blind procedure was not fully achieved: the initial bundle retrieval exposed explanatory comments, including comments on the repaired constructibility definition and polynomial-time statements. I subsequently used comment-stripped sources for the declaration restatements below, but do not represent them as a fully blind reading.

Textbook comparisons use the supplied AB09 PDF: §1.2, PDF pp. 37–40/book pp. 11–14; Definition 1.3 and constructibility, PDF pp. 41–42/book pp. 15–16; model variations, PDF pp. 42–45/book pp. 16–19; timed universal simulation, PDF p. 47/book p. 21; Definitions 1.12–1.13, PDF p. 51/book p. 25; Definition 3.4, PDF p. 99/book p. 73. The constructibility and oracle-definition pages were also inspected visually.

The thirteen changed/new declarations have the following meanings.

| File · declaration | Mathematical restatement | Source and round-1 comparison |
|---|---|---|
| `Finite.lean · MultiTapeTM.output_length_le` | For any raw machine and input, its output after \(t\) iterations from initialization has at most \(t\) symbols. Neither halting nor finite state/alphabet types is assumed. | Correct for the append-only model; it is a model-specific sanity statement, not an identification with AB's output-tape contents. |
| `Finite.lean · MultiTapeTM.output_prefix` | From any starting configuration, the output at an earlier time is a list prefix of the output at a later time. | Correct even with pre-existing output, arbitrary work-tape contents, or an already halted state. |
| `Finite.lean · FinTM.not_computesInTime_zero` | No bundled machine, on any input, produces any specified output and halts within zero iterations of its initialized run. | Correct: initialization has state `some q₀`. Already halted arbitrary configurations are irrelevant to this initialized predicate. |
| `Oracle.lean · OracleTM.WellFormed` | The designated query, yes, and no states are pairwise unequal. No condition is imposed on the initial state or on finiteness. | Correct faithful designation of AB's three special states. It properly permits `q₀ = qQuery`. |
| `Oracle.lean · ofMultiTapeTM_wellFormed` | Every ordinary-machine embedding satisfies that pairwise-distinctness predicate. | Correct: the designated states are `Sum.inr 0`, `Sum.inr 1`, and `Sum.inr 2` in `State ⊕ Fin 3`. |
| `Oracle.lean · queryString_length_le` | After \(t\) iterations of an initialized oracle run, the extracted query has length at most \(t\), for every oracle and raw machine. | Correct without `WellFormed`. Exclusion of the blank-free fallback requires the stronger support invariant discussed below. |
| `Oracle.lean · plainEmptyOracle` | Construct a raw ordinary machine on the same state type and all \(k+1\) work tapes; replace the query state's transition by a stationary transition to `qNo`, and retain every other transition. | Implements removal of the empty oracle without encoding or additional steps. It is not a finite-machine bundle or an inverse that removes the extra tape. |
| `Oracle.lean · runFrom_plainEmptyOracle` | From every configuration and for every \(t\), the constructed ordinary run and the original empty-oracle run have exactly equal configurations. | Correct without initialization, finite support, or `WellFormed`. This is the missing converse sanity statement from round 1. |
| `DTIME.lean · DTIME_eq_empty_of_exists_zero` | If a bound vanishes at even one natural input length, no binary language belongs to its `DTIME` class. | Correct for the all-length, multiplicative-bound convention. This explains the need for small-input padding. |
| `P.lean · mem_P_iff` | A language belongs to the padded union defining `P` exactly when one finite binary machine decides it within \(C(n+1)^d\) steps on every input, for some natural constants \(C,d\). | Correct characterization of polynomial time in this model; both zero length and degree zero are included. A zero \(C\) cannot be a witness. |
| `P.lean · dtime_one_subset_P` | Every language decidable in some constant number of steps belongs to `P`. | Correct. `DTIME 1` means an arbitrary fixed constant bound, not necessarily one step. |
| `TimeConstructible.lean · TimeConstructible` | \(T(n)\ge n\) for all \(n\), and there are one positive natural constant \(c\) and one finite binary machine that, on every input \(x\), halt with `(T x.length).bits` within \(c(T(\lvert x\rvert)+1)\) steps. | The uniform quantifier order is correct. The budget intentionally differs from AB's literal upper bound; the added \(1\) covers \(T(0)=0\). |
| `TimeConstructible.lean · timeConstructible_id` | The identity function satisfies that repaired definition. | True, including the empty input and little-endian append-only output. An explicit witness appears below. |

Every row of the resolution changelog was checked.

| Round-1 item | Disposition of the resolution |
|---|---|
| 1 — strict constructibility | The definition is repaired, and the new identity statement is true. The module introduction and blanket example language still need the prose corrections in finding 1. |
| 2 — coinciding oracle states | `WellFormed` supplies the intended faithful-interface condition, and the ordinary embedding satisfies it. None of the new raw semantic statements needs that hypothesis. Qualify the informal looping examples as in finding 5. |
| 3 — query-tape overhead | The false constant-overhead equivalence is removed. Polynomial-overhead equivalence is correct, and the cited structured parity family gives the claimed separation; details below. |
| 4 — undeclared model changes | `DTIME.lean` now explicitly declares append-only output and changed initialization; the bundle also records the input-head clamp. Simulations remain phase-2 obligations. The plan retains conflicting descriptions, identified in finding 4. |
| 5 — oracle citation | The source-facing citations now identify Definition 3.4, matching PDF p. 99. Historical references to the old error in the changelog/findings are harmless. |
| 6 — fresh-state behavior | The revised `ofMultiTapeTM` docstring correctly distinguishes the transition table from the query override. Starting in the fresh query state takes one answer step, then one halting step. |
| 7 — `P` prose | The union is now padded and the theorem's hypothesis is correctly called pointwise. The newly added machine-patching claim is false, and the vanishing-power explanation needs an explicit positive-degree qualification; see findings 2–3. |
| 8 — plan sections 3.1–3.2 | State-only finiteness, separate alphabet hypotheses, and the future finite oracle bundle are now accurately described. Both directions of the raw simulation are present, including the newly added exact empty-oracle elimination. |
| 9 — halting/output sanity | The added zero-time and output statements express the intended nontrivial semantics. They do not introduce an alternative acceptance convention. |
| 10 — oracle sanity | Query length and converse simulation were added. The stronger cell-blankness fact is mathematically valid but is not itself the conclusion of the new length theorem; see finding 6. |
| 11 — polynomial/PAL sanity | `mem_P_iff` and constant-time inclusion were added correctly. Both inherited palindrome statements are unchanged; the full previous sanity menu was explicitly deferred rather than claimed complete. |

The inherited statements were checked textually, without repeating their round-1 audits.

| File | Inherited `sorry` statements | Comparison |
|---|---|---|
| `Finite.lean` | `ComputesInTime.mono` | Exact match |
| `Oracle.lean` | `step_eq_of_ne_qQuery`; `runFrom_ofMultiTapeTM`; `computesInTime_ofMultiTapeTM` | All three exact matches |
| `DTIME.lean` | `DTIME.mono` | Exact match |
| `P.lean` | `mem_P_of_dtime_le` | Exact match |
| `Examples.lean` | `PAL_mem_DTIME_linear`; `PAL_mem_P` | Both exact matches |

There are exactly eight new `sorry` statements, giving sixteen in total. Each new statement is mathematically true as written; these dispositions do not fill its Lean proof.

| New `sorry` | Individual disposition |
|---|---|
| `MultiTapeTM.output_length_le` | **True.** Initially the output is empty. One step concatenates an optional symbol's list, of length at most one; induction gives length at most \(t\), including absorbed halting steps. |
| `MultiTapeTM.output_prefix` | **True.** Every step replaces the existing output by its concatenation with a list. Iterate this prefix relation for \(t'-t\) steps after time \(t\), using `runFrom_add` and transitivity; no initialization assumption is needed. |
| `OracleTM.queryString_length_le` | **True.** After \(t\) steps, all work heads have absolute position at most \(t\), and every nonblank cell has absolute index strictly less than \(t\). Induct using writes at the old head position; oracle-answer and halted steps leave tapes unchanged. Consequently cell \(t\) is blank, the first nonnegative blank is at most \(t\), and the extracted prefix has length at most \(t\). |
| `OracleTM.runFrom_plainEmptyOracle` | **True.** The two one-step maps agree on halted, query, and other states. At a query both change only the state to `some qNo`, as the field calculation below verifies. Equality of all iterates follows by induction, without state-distinctness assumptions. |
| `DTIME_eq_empty_of_exists_zero` | **True.** Given \(T(n)=0\), instantiate any claimed decider at `List.replicate n false`. Its budget is \(cT(n)=0\), contradicting `not_computesInTime_zero`, for every constant \(c\). |
| `mem_P_iff` | **True.** Forward, retain the machine and degree and replace its constant \(a\) by \(2a\). Backward, retain the machine and degree and replace \(C\) by \(C2^d\). The inequalities below justify both replacements for every natural \(n,d\), including zero. |
| `dtime_one_subset_P` | **True.** For a constant-time witness \(a,M\), \(a\le a(n+1)\) on every input length. The same machine belongs to the degree-one component of the padded union. |
| `timeConstructible_id` | **True.** Maintain the binary count on one work tape, return to its origin using the untouched blank at cell \(-1\), and emit its bits only after counting is complete. The explicit four-state table below uses at most \(5(n+1)\) steps and emits exactly `n.bits`. On empty input it emits nothing and halts in two steps. |

The following calculations answer the seven specific questions.

For question 1, a concrete identity witness uses one work tape and four active states `count`, `carry`, `rewind`, `emit`. Start in `count` with the prescribed blank tape and head at zero. Here “bit” means either Boolean value, “blank” means `none`, and “keep” means no write; all writes occur before the listed head movements. The table covers every combination of state and scanned symbols.

| State | Input read | Work read | Work write | Input move | Work move | Emitted symbol | Next state |
|---|---|---|---|---|---|---|---|
| `count` | blank | any | keep | 0 | 0 | none | `emit` |
| `count` | bit | true | false | +1 | +1 | none | `carry` |
| `count` | bit | false or blank | true | +1 | −1 | none | `rewind` |
| `carry` | any | true | false | 0 | +1 | none | `carry` |
| `carry` | any | false or blank | true | 0 | −1 | none | `rewind` |
| `rewind` | any | bit | keep | 0 | −1 | none | `rewind` |
| `rewind` | any | blank | keep | 0 | +1 | none | `count` |
| `emit` | any | bit \(b\) | keep | 0 | +1 | \(b\) | `emit` |
| `emit` | any | blank | keep | 0 | 0 | none | halt |

After completing \(m\) increments, for \(0\le m\le n\), the machine is in `count`, its input head is at \(m+1\), its work head is at zero, its output is empty, and its work tape contains exactly `m.bits` starting at zero, with all other cells blank. This holds initially for \(m=0\).

If \(m<n\), let \(r\) be the number of initial true bits in `m.bits`. The next increment flips those \(r\) bits to false and changes the following false/blank cell to true. For some natural \(v\),
\[
m=(2^r-1)+2^{r+1}v
\quad\Longrightarrow\quad
m+1=2^r+2^{r+1}v.
\]
Thus the updated contiguous nonblank region is exactly `(m+1).bits`. The rewind crosses \(r\) nonblank cells, reaches the untouched blank at \(-1\), and moves right once; the head does not need a stored unbounded index or a fourth alphabet symbol. The input head advanced exactly once, and only when \(m<n\), so clamping does not alter this invariant.

The increment uses \(r\) carry transitions, one final write, \(r\) rewind transitions, and one return transition:
\[
r+1+r+1=2r+2.
\]
Across increments from \(0\) through \(n-1\), the number having at least \(j\) trailing ones is \(\lfloor n/2^j\rfloor\). Therefore
\[
\sum_{m=0}^{n-1}2\bigl(1+\text{number of trailing ones of }m\bigr)
=
2n+2\sum_{j\ge1}\left\lfloor\frac n{2^j}\right\rfloor
\le 2n+2n=4n.
\]
The sum is finite because its terms eventually vanish. At \(m=n\), the next input symbol is blank; one transition enters `emit`, then the machine emits exactly the stored bits from cell zero upward and halts at their first following blank. For \(n\ge1\), the output length is at most \(n\) (equivalently \(n<2^n\), proved by induction), while `0.bits=[]`. Hence, for every \(n\),
\[
\text{total steps}
\le 4n+\operatorname{length}(n.\mathrm{bits})+2
\le 5n+2
\le 5(n+1).
\]
This supplies the positive constant \(c=5\) and a finite state type. In particular, \(n=0\) takes two transitions and emits `[]`; \(n=1,2,3,4\) take \(5,10,12,19\) transitions and emit `[true]`, `[false,true]`, `[true,true]`, `[false,false,true]` respectively. A separate executable transcription checked 3,081 initialized runs, including every Boolean word of length at most ten and carry boundaries through length 8,193; this is supplemental validation, not a Lean proof.

The repaired definition supplies an exact *value* \(T(n)\), despite allowing slack in the constructor's running time. A timed simulator can first compute/store those bits on work tape, rewind its input, and then count simulated transitions against that value; buffering a simulated output is also available when a failure result must be emitted on timeout. Construction and rewind cost \(O(T(n)+1)\), and an elementary binary clock costs at most \(O((T(n)+1)\log(T(n)+2))\); this fits the planned relaxed quadratic simulation, and the efficient simulation's asymptotic budget as well. On positive input lengths \(T(n)\ge n\ge1\), so \(T(n)+1\le2T(n)\). No additional Chapter-1 obstruction is introduced by the repair, but exact numerical constants must still be derived.

AB's timed-universal-machine paragraph on PDF p. 47 actually supplies the numerical budget as an extra input. That explicit-budget construction does not require time constructibility; constructibility is relevant when the simulator must itself generate a bound depending on input length. The module should distinguish these uses rather than attribute the extra hypothesis to that paragraph.

For questions 2 and 7, the three inequalities have distinct roles.

* `qQuery ≠ qYes` and `qQuery ≠ qNo` ensure that either answer reaches an ordinary table state.
* `qYes ≠ qNo` ensures that the answer can carry a Boolean distinction. If they coincide, then for every configuration and all oracles,
  \[
  M.\mathrm{step}\ O_1\ \mathrm{cfg}
  =
  M.\mathrm{step}\ O_2\ \mathrm{cfg},
  \]
  since both query branches give the same state and all other branches are oracle-independent. Induction gives equal runs, so such a machine ignores the oracle.
* Pairwise distinctness is therefore appropriate for the faithful three-state interface, although it is stronger than what raw stepping or empty-oracle elimination needs. Permitting answer-state equality as an additional raw case would not invalidate any new theorem or enlarge the computational power of the intended existential oracle classes; those machines can be simulated ordinarily.
* No `WellFormed` machine can have `State = Fin 2`: its three designated states would give an injection `Fin 3 → Fin 2`. `Fin 3` suffices, and `q₀=qQuery` is allowed. With this initialization the first query is empty; oracle `{[]}` reaches `qYes` and the empty oracle reaches `qNo`.
* If `qNo=qQuery`, the empty-oracle step fixes every query-state configuration, as does the ordinary replacement action. Thus the lockstep theorem remains true even when both runs loop there forever. With all states in `Fin 1`, both initialized runs are fixed from the start. An empty state type cannot instantiate a machine because the structure requires `q₀`.

The looping descriptions need qualifications: `qYes=qQuery` loops after a **positive** response; a negative response can reach a distinct `qNo` and halt normally. Likewise, when the three designated states coincide, their common state loops once reached, but an unrelated initial state can execute ordinary transitions and halt without querying.

For question 3, write \(a\) for the stationary action used by `plainEmptyOracle`. For any configuration, its five fields after application are
\[
\begin{aligned}
(a.\mathrm{apply}\ \mathrm{cfg}).\mathrm{state}
  &=\mathrm{some}\ M.qNo,\\
(a.\mathrm{apply}\ \mathrm{cfg}).\mathrm{inputPos}
  &=\mathrm{moveInputPos}(\mathrm{cfg.inputPos},0)
    =\mathrm{cfg.inputPos},\\
(a.\mathrm{apply}\ \mathrm{cfg}).\mathrm{workTapes}(i)
  &=\mathrm{cfg.workTapes}(i),\\
(a.\mathrm{apply}\ \mathrm{cfg}).\mathrm{workTapePos}(i)
  &=\mathrm{cfg.workTapePos}(i)+0
    =\mathrm{cfg.workTapePos}(i),\\
(a.\mathrm{apply}\ \mathrm{cfg}).\mathrm{output}
  &=\mathrm{cfg.output}\mathbin{++}[]
    =\mathrm{cfg.output}.
\end{aligned}
\]
For input position \(p\in\mathrm{Fin}(n+2)\), the intermediate integer calculation is
\[
((p.\mathrm{val}:\mathbb Z)+0).\mathrm{toNat}=p.\mathrm{val}<n+2.
\]
Thus the clamp returns \(p\), including \(p=0\), \(p=n+1\), and both positions when \(n=0\). The outer no-write `none` leaves each whole work-tape function unchanged; it does not erase the scanned cell.

At a query the empty oracle always answers no, so this is exactly its record update. At a nonquery active state both semantics apply the same table action; at a halted state both return the original configuration. Consequently their one-step functions and all their iterates are equal. This proof also covers arbitrary infinitely supported tapes and the blank-free fallback.

For question 4, let \(\mathrm{cfg}_t=M.\mathrm{runFrom}\ O\ (M.\mathrm{initCfg}\ x)\ t\). Simultaneous induction gives
\[
\forall i,\quad
\lvert\mathrm{cfg}_t.\mathrm{workTapePos}(i)\rvert\le t,
\qquad
\forall i,z,\quad
\mathrm{cfg}_t.\mathrm{workTapes}(i)(z)\ne\mathrm{none}
\Longrightarrow \lvert z\rvert<t.
\]
At zero, the first assertion is \(0\le0\), and the second is vacuous because all tapes are blank. In an ordinary successor step, an old nonblank cell still satisfies the strict bound for \(t+1\), and the only possible new nonblank cell is at the **old** head position, whose absolute value is at most \(t<t+1\). Each head moves by at most one; halted and oracle-answer steps preserve the invariant.

Taking \(z=t\) gives
\[
\mathrm{cfg}_t.\mathrm{workTapes}(\mathrm{Fin.last}\ k)(t)=\mathrm{none}.
\]
The least nonnegative blank is therefore at most \(t\), and every cell preceding it is nonblank; `filterMap` deletes none of those entries. This proves the length statement and separately rules out the fallback. The sketch's radius \(t-1\) is correct for writes during a positive number \(t\) of steps, and there are no writes at \(t=0\). It would not follow from a move-before-write model, but `Action.apply` explicitly writes before moving. For example, writing true at zero and moving right in the first step leaves head position one and the only nonblank cell at zero.

The length inequality alone does not logically certify that the fallback was avoided: that branch returns the empty list and also satisfies every nonnegative length bound. The stronger cell-blankness fact above should be retained as a lemma if downstream proofs need that certificate.

For question 5, since \(n\le n+1\) and \(1\le(n+1)^d\), for every \(n,d\in\mathbb N\),
\[
n^d+1\le(n+1)^d+(n+1)^d=2(n+1)^d.
\]
Multiplication by \(a\ge0\) gives the forward budget
\[
a(n^d+1)\le(2a)(n+1)^d.
\]
For the reverse bound, at \(n=0\),
\[
(0+1)^d=1\le2^d(0^d+1);
\]
when \(d=0\) the right side is \(2\), and when \(d>0\) it is \(2^d\). At \(n\ge1\),
\[
(n+1)^d\le(2n)^d=2^d n^d\le2^d(n^d+1).
\]
Multiplying by \(C\) proves the reverse budget using \(C2^d\). In particular, at \(d=0\) the first inequality is \(2\le2\) and the second is \(1\le2\), for every \(n\). No positivity premise on \(a,C,d\) is needed for the arithmetic; a zero time constant simply cannot witness a decider.

The polynomial docstring's machine-patching claim is unnecessary even for eventual domination. If \(T(n)\le c(n^d+1)\) for every \(n\ge N\), choose
\[
c'=\max\bigl(\{c\}\cup\{T(m):m<N\}\bigr).
\]
For \(n<N\), \(T(n)\le c'\le c'(n^d+1)\); for \(n\ge N\), the eventual bound gives the same inequality. An existing `DTIME T` witness \(a,M\) therefore has budget at most \(ac'(n^d+1)\) everywhere, with the **same machine**.

For question 6, the asymmetric generality is correct:
\[
\operatorname{length}((M.\mathrm{runFrom}\ \mathrm{cfg}\ t).\mathrm{output})
\le\operatorname{length}(\mathrm{cfg.output})+t.
\]
The stated initial-run theorem specializes the initial length to zero. Dropping initialization without adding that term is false already at \(t=0\) with `cfg.output=[true]`. Prefix monotonicity needs no such restriction; it holds from every configuration, including a halted one, where all later outputs are equal.

The query-tape overhead correction was also checked substantively. An auto-erasing machine can simulate a persistent query tape by keeping a shadow work tape and copying the current query before each call. Conversely, a persistent machine can implement erasure by clearing the finite visited interval, using bookkeeping tapes. In a run of \(t\) simulated steps, the necessary intervals have length \(O(t+1)\), and there are at most \(t\) calls, giving polynomial total overhead.

The separation uses the **specific** family of length-\(n\) words with exactly one zero. A persistent machine writes the all-one word once, moves the zero through its \(n\) positions, and accumulates oracle-answer parity in \(O(n+1)\) steps. On its empty-oracle execution, any uniformly correct machine must query every word in the family: otherwise adding an omitted word to the oracle changes the required answer without changing the observed transcript. With automatic erasure, each such length-\(n\) query requires \(n\) fresh writes, so the total is at least \(n^2\). This supports the corrected polynomial equivalence; it does not assert linear-time preparation for arbitrary families of \(n\) unrelated words.

The remaining findings are as follows. No blocker or major was found in the audited changes; the five minor findings below concern prose. This does not certify the unfilled proofs, the deferred model simulations, or the future finite oracle interface.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `TimeConstructible.lean · module introduction and Design` | The prose still mixes the old strict definition with the repair and overstates restoration of all literal examples. | The opening says “within `T \|x\|` steps,” whereas the declaration uses \(c(T(n)+1)\). The remaining condition \(n\le T(n)\) still excludes literal \(T(n)=n\lceil\log_2 n\rceil\) at \(n=1\). The explicit-budget timed universal machine does not itself need constructibility. | State the repaired budget in the opening; say “at most,” rather than suggesting exact halting time; qualify examples by small-input normalization, and distinguish supplied budgets from generated bounds. |
| 2 | minor | `P.lean · mem_P_of_dtime_le` docstring | Eventual domination does not require patching an already globally correct machine. | The finite maximum \(c'\) constructed above yields a pointwise bound; multiplying the existing time constant suffices. | Replace “requires patching the machine” by “requires absorbing finitely many exceptional bounds into the constant.” The current theorem may remain pointwise. |
| 3 | minor | `P.lean · module introduction and Design` | The vanishing-power explanation needs an explicit positive-degree restriction. | In Lean, \(0^0=1\). Every positive-degree unpadded component is empty, but the degree-zero component is `DTIME 1` and contains the two constant languages. Thus the unpadded union over all natural degrees is `DTIME 1`, not empty. | Say “every positive-degree component” and explicitly identify the empty union as AB's \(d\ge1\) union. Keep the padded definition and `mem_P_iff`. |
| 4 | minor | `AroraBarakChapter1Plan.md` · sections 1–2 and module layout; `Finite.lean · FinTM` docstring | Some source-facing descriptions still contradict the declared model deviations. | The plan's §1 attributes write-only output to AB §1.2, whose output tape is read-write (PDF pp. 37–38). The module layout still promises `PAL ∈ DTIME(3n)`, but that class is empty at length zero. `FinTM` is still called “the machine of [AB09, §1.2]” without its model-variation qualification. | Describe the port as a declared variation, link to `DTIME.lean`'s deviations, and change the PAL target to `DTIME (n+1)`. |
| 5 | minor | `Oracle.lean · OracleTM / WellFormed` explanatory comments | The aliasing warnings omit the answer/reachability conditions under which looping occurs. | With `qYes=qQuery` and distinct `qNo`, a negative answer can reach a halting table row. With all three designated states equal but `q₀` different, the initial table row can halt without a query. | Say “after a positive answer” and “once the common query state is reached.” Retain the pairwise-distinctness definition. |
| 6 | note | `Oracle.lean · queryString_length_le` | The length theorem is true, but its conclusion alone does not certify exclusion of the fallback. | The fallback returns `[]`, whose length also satisfies the bound. The initialized cell-\(t\)-blank invariant independently proves unreachability, including \(t=0\). | No change to the length statement is needed. Expose the stronger blankness lemma when downstream code needs the certificate. |
| 7 | note | All eight new `sorry` statements; `WellFormed` and empty-oracle elimination | The new statements survive the required adversarial cases with their current hypotheses. | The individual dispositions, explicit counter witness, field calculation, and polynomial inequalities above cover every new `sorry`. `WellFormed` is unnecessary for raw lockstep but appropriate at the future faithful interface. | Complete the existing proofs without weakening their statements; retain the planned finite, well-formed oracle interface and phase-2 simulation obligations. |

Notation glossary: \(M\) is a machine; \(O,O_1,O_2\) are oracle languages; \(T\) is a natural-valued time-bound function; \(x\) is an input word; \(n=\lvert x\rvert\) is its length; \(t,t'\) are step counts; \(k\) is the number of ordinary work tapes; \(i\) is a tape index; \(z\) is an integer cell position; \(p\) is an input-head position; \(\mathrm{cfg},\mathrm{cfg}_t\) are configurations, with \(\mathrm{cfg}_t\) defined above; \(m\) is the number of completed increments (or a finite-range index in the maximum); \(r\) counts trailing binary ones; \(v\) is the remaining high-order integer in the increment calculation; \(j\) indexes carry lengths; \(b\) is a bit; \(a,c,c',C\) are natural time constants, except that \(a\) locally names the stationary action in the field calculation; \(d\) is a polynomial degree; \(N\) is an eventual-bound threshold. \(\operatorname{length}\) is list length, \(++\) is list concatenation, \(\lfloor\cdot\rfloor,\lceil\cdot\rceil\) are floor/ceiling, and \(\log_2\) is binary logarithm. `count`/`carry`/`rewind`/`emit` name the four states of the explicit counter. Other code notation retains the meanings in the audited sources; \(O(\cdot)\) denotes asymptotic upper bounds.
