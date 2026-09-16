# Phase 1 external statement audit

Audited branch: `complexity/arora-barak-ch1`, pinned at [65a3fe52774bd3ada3f66fd1509dcd1bbf7a6bc8](https://github.com/Shilun-Allan-Li/tcslib/tree/65a3fe52774bd3ada3f66fd1509dcd1bbf7a6bc8). All eight attached Lean files match the repository blobs byte-for-byte. This report covers 44 explicit definitions/structures/abbreviations and all eight `sorry` statements, plus the supplied architecture and policy documents.

This is a mathematical statement audit, not Lean elaboration or kernel verification. No tactic-script audit was performed. Restatements were recorded from comment-stripped code before consulting its explanatory comments, except that the initial repository retrieval exposed the comments in `DTIME.lean`; the requested blind-reading procedure therefore has that exception.

Source locations refer to the supplied Arora–Barak PDF: §1.2, book pp. 11–14/PDF pp. 37–40; Definition 1.3, p. 15/PDF p. 41; time constructibility, p. 16/PDF p. 42; model variations, pp. 16–19/PDF pp. 42–45; Definitions 1.12–1.13, p. 25/PDF p. 51. The oracle-machine definition is **Definition 3.4**, p. 73/PDF p. 99, not Definition 3.6. Both the time-constructibility and oracle-definition pages were checked visually.

## Per-definition restatements and source comparison

The following restatements describe the code's meaning; the comparison column distinguishes textbook content from implementation conventions.

### Configuration.lean — 10 declarations

[Pinned source](https://github.com/Shilun-Allan-Li/tcslib/blob/65a3fe52774bd3ada3f66fd1509dcd1bbf7a6bc8/TCSlib/Complexity/TuringMachine/Configuration.lean)

| Declaration | Mathematical restatement | Source comparison |
|---|---|---|
| `Action` | One signed input-head move; an optional write and signed move for each work tape; zero or one emitted symbol; and a successor state or halt. An outer write `none` leaves the cell alone; `some none` erases it. | Implements transition data from §1.2. Append-only output is a variation: AB's output tape is read-write. |
| `Cfg` | A possibly halted state, an input position between 0 and input length plus one, integer-indexed work tapes and heads, and an output list. Arbitrary configurations may have infinitely many nonblank cells. | More general than reachable textbook configurations; intentional for raw semantics. Input clamping, bidirectionality and output representation are model choices. |
| `moveInputPos` | Add −1, 0 or 1 to the input position, saturating at 0 and at input length plus one. | Correctly implements the declared clamp; does not wrap at the boundary. AB allows an unbounded blank suffix. |
| `Cfg.inputSymbol` | Positions 0 and input length plus one read blank; position j inside the string reads its element j−1. | Implements the declared absence of a start-marker symbol. |
| `Cfg.workTapeSymbols` | Read each work tape at its current head position. | Corresponds to the simultaneous reads in §1.2. |
| `Cfg.Halted` | The state is `none`. | A representation of AB's single halting state. |
| `Cfg.init` | Start in `some q₀`, with input position 1, blank work tapes, work heads at 0 and empty output. | Unlike AB, there are no start-marker cells and the input head begins on the first input symbol; for empty input it begins on the right blank. Initial configurations are never halted. |
| `Action.apply` | Set the successor state, clamp the input move, write at each old work-head position before moving that head, and append the optional output symbol. | Correct transition ordering. This primitive can act on halted configurations; the machine's `step`, not `apply`, enforces absorption. |
| `visitedOfCfgs` | For each tape, collect the distinct head positions in a supplied finite configuration list. | Technical space-accounting definition, not a Chapter 1 claim. |
| `spaceUsedOfCfgs` | Sum those numbers of distinct positions across work tapes. | Counts visited cells, excluding input/output; it does not count only nonblank cells. The vendored documentation declares that distinction. |

### Deterministic.lean — 15 declarations

[Pinned source](https://github.com/Shilun-Allan-Li/tcslib/blob/65a3fe52774bd3ada3f66fd1509dcd1bbf7a6bc8/TCSlib/Complexity/TuringMachine/Deterministic.lean)

| Declaration | Mathematical restatement | Source comparison |
|---|---|---|
| `MultiTapeTM` | An initial state and a total transition function of the current state and scanned input/work symbols. Neither alphabet nor state type is required to be finite. | A raw generalization of §1.2, not by itself the textbook finite-machine object. |
| `step` | Leave a halted configuration unchanged; otherwise choose and apply its transition action. | Faithful absorbing halting semantics. |
| `outputSymbol` | The next transition's optional emitted symbol, or no symbol if already halted. | Technical helper for append-only output; it is not the last symbol already emitted. |
| `initCfg` | Use `Cfg.init` with this machine's initial state. | Inherits the declared initialization variations. |
| `runFrom` | Iterate `step` t times from the supplied configuration. | Exactly t iterations, but not necessarily t active transitions: halted configurations repeat. |
| `visitedByTapeHead` | Positions occupied by one head at times 0 through t, including both endpoints. | Deliberate visited-cell measure. |
| `spaceUsedByTape` | Cardinality of that visited-position set. | In particular, it is one at time zero for each existing work tape. |
| `spaceUsed` | Sum the individual work-tape counts. | Thus space at time zero is k, and space for k=0 is zero. |
| `ComputesInTimeAndSpace` | At time t, the initial run is halted with exactly the specified output, and its visited-cell count is exactly s. | The time argument is an upper bound because halting absorbs; the space argument is an exact count. This distinction is consistent with the code's docstring. |
| `ComputesFunInTimeAndSpace` | On every encoded argument, produce its encoded function value at some time and space no greater than the supplied input-dependent bounds. | A generalization of Definition 1.3 to explicit encodings and space bounds. The machine is fixed before the universal input quantifier. |
| `ComputableInTimeAndSpace` | There exist a tape count, a finite state type, and a binary machine satisfying the preceding property. | Finiteness is enforced here. The arbitrary supplied injections make this a statement relative to encodings, not an assertion that encoding conversion is computable. |
| `ComputableInTimeAndSpaceOfLength` | Use bounds that depend on encoded input length in the preceding definition. | Matches the length-based form of Definition 1.3, relative to those encodings. |
| `indicator` | The classical Boolean characteristic function of a set. | The target function from §1.6; defining it does not give a machine membership access. |
| `DecidableInTimeAndSpace` | Compute that characteristic function using the supplied input encoding and a singleton Boolean output. | A decision-problem specialization with space accounting. |
| `haltsAtStep` | Halted at t but not at truncated predecessor t−1. | This alone expresses first halting at exactly t; it is false at t=0. The downstream time-class definitions do not replace their upper-bound semantics with this predicate. |

### Finite.lean — 3 declarations

[Pinned source](https://github.com/Shilun-Allan-Li/tcslib/blob/65a3fe52774bd3ada3f66fd1509dcd1bbf7a6bc8/TCSlib/Complexity/TuringMachine/Finite.lean)

| Declaration | Mathematical restatement | Source comparison |
|---|---|---|
| `FinTM` | Bundle a tape count, a state type with `Fintype` and `DecidableEq` data, and a raw machine. | Supplies finite states; `q₀` also forces the state type to be inhabited. It does not supply alphabet finiteness. This is safe for the audited classes, which fix `Bool`; general alphabet theorems must add finiteness. Plan §3.2 inaccurately says alphabet finiteness is bundled too. |
| `ComputesInTime` | Existentially discard the exact space count: the initial run is halted at t with precisely the specified output. | Correct “within t” semantics for Definition 1.3 in this model. |
| `ComputesFunInTime` | One fixed machine has that behavior for every string, under a length-dependent time bound. | Correct uniform quantifier order for Definition 1.3. |

### Oracle.lean — 11 declarations

[Pinned source](https://github.com/Shilun-Allan-Li/tcslib/blob/65a3fe52774bd3ada3f66fd1509dcd1bbf7a6bc8/TCSlib/Complexity/TuringMachine/Oracle.lean)

| Declaration | Mathematical restatement | Source comparison |
|---|---|---|
| `OracleTM` | Four designated state values—start, query, yes, no—and an ordinary transition function over k+1 work tapes. No distinctness or finiteness is required. | Raw finiteness deferral is declared; allowing the three special states to coincide conflicts with the advertised ordinary answer-state behavior. AB calls them three special states. |
| `queryTapeIdx` | The last of the k+1 work tapes. | Technical representation of the special tape in Definition 3.4. |
| `queryString` | Read the nonnegative prefix ending immediately before its first blank; return `[]` if no nonnegative blank exists. | AB leaves extraction implicit. Before the least blank, `filterMap` removes nothing. The exceptional branch is unreachable from initialization; negative cells and material after the delimiter are not part of the current query. |
| `step` | Fix halted configurations; at the query state change only the state according to oracle membership; otherwise execute the ordinary transition. | The one-step answer and unchanged tapes implement Definition 3.4. Answer-state aliases with the query state are a missing well-formedness restriction. |
| `initCfg` | Start in the designated initial state with all k+1 work tapes blank and heads at zero. | The query tape initially encodes the empty word. Starting in the query state immediately queries that word. |
| `runFrom` | Iterate the oracle-dependent step t times from the supplied configuration. | Standard oracle operational semantics, including arbitrary raw starting configurations. |
| `ComputesInTime` | At t, the initial oracle run is halted and its complete output equals the requested string. | Correct upper-bound semantics; this is a property of a raw machine, not a finitely bundled oracle complexity class. |
| `Action.extend` | Add a last tape with no write and no movement; preserve the other action fields. | Technical embedding helper. |
| `Action.mapState` | Apply a function to nonhalting successor states; preserve halt and every other action field. | Technical state-renaming helper; injectivity is unnecessary for this definition. |
| `Cfg.embedOracle` | Map old states into `Sum.inl`, add a blank last tape with head zero, and preserve the other fields. | Correct embedding, including arbitrary old tape contents and already halted states. |
| `ofMultiTapeTM` | Use left-summand ordinary states and three fresh right-summand oracle states; extend old transitions by leaving the new tape untouched. | Fresh states are unreachable from embedded configurations. Its docstring's assertion that it “halts immediately from the fresh states” needs qualification: the query state's special semantics overrides its ordinary halting action. |

### ClassP files — 5 declarations

| File · declaration | Mathematical restatement | Source comparison |
|---|---|---|
| `DTIME.lean · FinTM.DecidesInTime` | On every binary input, halt within the prescribed bound and output exactly the singleton membership bit. | Matches §1.6. A longer output string is not a Boolean result. |
| `DTIME.lean · DTIME` | One natural constant and one finite binary machine must decide the language on every input within that constant times T(length). | Correct Definition 1.12 quantifiers. Zero constants cannot witness membership; positive real constants, if allowed, can be rounded upward. A zero value of T at even one input length makes the class empty. |
| `TimeConstructible.lean · TimeConstructible` | T(n) is at least n, and one finite binary machine outputs `Nat.bits (T n)` on every length-n input within T(n) steps. | Reproduces the literal bound on p. 16, but is incompatible with the stated examples in this model: identity is excluded, even away from zero. `Nat.bits 0=[]` and the bits are least significant first. |
| `P.lean · P` | Union over natural exponents c of `DTIME (n^c+1)`. | A sound normalization of intended polynomial time. It is not equal to the literal unpadded union under the present all-input semantics. The opening module sentence still states that unpadded union. |
| `Examples.lean · PAL` | All binary lists equal to their reversals, including the empty list. | Exactly the language corresponding to Examples 1.1 and 1.4. |

## Individual dispositions of the eight `sorry` statements

These are mathematical proof arguments, not completed Lean proofs.

| Statement | Disposition and argument |
|---|---|
| `Finite.lean · ComputesInTime.mono` | **True as stated.** Factor the run to t′ through t using t′=t+(t′−t); the configuration at t is halted, so its state and output never change. For the existential space witness, take the actual space used at t′. |
| `Oracle.lean · step_eq_of_ne_qQuery` | **True as stated.** If the state is `none`, both steps return the configuration. Otherwise the hypothesis rules out the query branch, so both steps apply the same ordinary action independently of the oracle. |
| `Oracle.lean · runFrom_ofMultiTapeTM` | **True as stated.** Embedded states are `none` or `some (Sum.inl q)`, never the fresh query state. In the nonhalting case, the old tape reads agree, the mapped/extended action reproduces the old update, and the extra tape stays blank with head zero; induction on t proves the equality. This also works for k=0 and arbitrary, possibly infinitely supported, old tapes. |
| `Oracle.lean · computesInTime_ofMultiTapeTM` | **True as stated.** The embedded initial configuration equals the oracle machine's initial configuration field by field. Apply the preceding run equality; mapping by `Sum.inl` preserves exactly whether the state is `none`, and embedding preserves output. |
| `DTIME.lean · DTIME.mono` | **True as stated.** Retain the same constant and machine, use c·T₁(n)≤c·T₂(n), and apply `ComputesInTime.mono` on each input. No positivity premise is needed for the inequality, and a zero constant cannot be an actual decider witness. |
| `P.lean · mem_P_of_dtime_le` | **True as stated.** If the original membership witness uses constant a, then a·T(n)≤(a·c)(n^d+1). The same machine and product constant witness membership in the degree-d component of P. The written hypothesis is pointwise, although the docstring says “eventually.” |
| `Examples.lean · PAL_mem_DTIME_linear` | **True as stated.** Use one work tape and the three active states `copy`, `rewind`, `test`, with the explicit boundary transitions below. Copy, rewind and successful comparison each take n+1 steps, giving 3(n+1); a mismatch halts earlier. For n=0 the three boundary transitions output `true`, so constant 3 witnesses the assertion on every input. |
| `Examples.lean · PAL_mem_P` | **True as stated.** Use the preceding result and the degree-one component, since n¹+1=n+1. The empty word is already covered by that bound. |

For the palindrome witness, the transitions relevant to initialized runs are as follows. Unmentioned output is absent and unmentioned tape writes are omitted; the input/work movements are simultaneous.

| State and read condition | Action |
|---|---|
| `copy`, input bit b | Write b on work tape; move both heads right; stay in `copy`. |
| `copy`, input blank | Move input left, keep work head still; enter `rewind`. |
| `rewind`, input bit | Move input left, keep work head still; stay in `rewind`. |
| `rewind`, input blank | Move input right and work head left; enter `test`. |
| `test`, input bit equals work bit | Move input right and work head left; stay in `test`. |
| `test`, input bit differs from work symbol | Emit `false` and halt. |
| `test`, input blank | Emit `true` and halt. |

After copying a length-n word the work cells 0,…,n−1 contain it, with other cells blank. Rewind positions the heads at input 1 and work n−1, including work −1 when n=0; subsequent comparisons therefore inspect opposite ends in order. The work tape's blank cell −1 substitutes for the book's start marker on these runs.

## Adversarial instantiations and counterexamples

1. **Zero work tapes, one active state, immediate halt.** Take k=0 and `State=Fin 1`. A transition that emits `true` and sets state to `none` decides every string in one step and uses zero work space; emitting `false` decides the empty language. Emitting nothing decides no language, since `[]` is never a singleton Boolean output. The halting transition can emit its bit in the same step.

2. **Zero time, including the empty input.** At time zero the state is `some q₀`, so for every machine, input and output,
   \[
   \neg M.\mathrm{ComputesInTime}(x,y,0).
   \]
   Consequently, `(∃ n, T n = 0) → DTIME T = ∅`: choose a binary word of that length, making c·T(n)=0 for every c. In particular `DTIME 0=∅`; c=0 contributes nothing to any `DTIME` definition.

3. **Constant time does not collapse to arbitrary languages.** The one-step, one-state machine may branch on the first scanned symbol, including the blank on empty input, so the class contains more than the two constant languages. Nevertheless a decider bounded by a fixed c can inspect no positive input position larger than c. Two sufficiently long words with the same first c bits have identical state/output histories through c steps, preventing arbitrary suffix-dependent languages from entering `DTIME 1`.

4. **Extra output symbols.** Any run producing `[false,true]` and halting fails the singleton-output specification for every proposed truth bit. Output only grows, so later padding of the time budget cannot repair it. This is the intended Boolean-result condition, not a defect; AB likewise requires the final output to be the Boolean result, although its read-write output tape may erase temporary work.

5. **Identity is not time constructible, even ignoring length zero.** Suppose the current definition had a witness for T(n)=n. On inputs `[false]` and `[false,false]`, the first transition is the same call
   \[
   M.\mathrm{tm.tr}\ M.\mathrm{tm.q}_0\ (\mathrm{some\ false})\ (\lambda i,\mathrm{none}).
   \]
   The length-one requirement forces that transition to halt with output `1.bits=[true]`. Its state and output on the length-two input are identical; absorption therefore preserves `[true]` through time two, contradicting `2.bits=[false,true]`. Independently, length zero fails because its time budget is zero. Thus
   \[
   \neg\mathrm{TimeConstructible}(\lambda n,n).
   \]

6. **Padding the function by one still does not fix exact constructibility.** Set T(n)=n+1 and compare `[false,false]` with `[false,false,false]`. The first two steps have identical state, work and output behavior, since neither run can read beyond position two before its third transition. Their required output strings are `3.bits=[true,true]` and `4.bits=[false,false,true]`; hence neither run can have emitted a bit by time two. The shorter run can emit at most one bit during its third step, but must have emitted two by its budget T(2)=3: contradiction.

7. **The strict definition is not wholly empty.** T(n)=2ⁿ has a k=0, `State=Fin 1` witness: for each input bit, emit `false` and move right; at the first blank, emit `true` and halt. Its output is n false bits followed by true, exactly `(2^n).bits`, and its time is n+1≤2ⁿ for every natural n, including n=0. This distinguishes the actual defect from wholesale triviality of the definition.

8. **Start in the query state.** With three distinct special states and `q₀=qQuery`, the blank initial query tape submits `[]` in the first step. For O={`[]`} the state becomes `qYes`; for O=∅ it becomes `qNo`, with tapes, heads and output unchanged. Ordinary answer-state transitions can then emit the appropriate bit and halt on step two. No rule requiring `q₀≠qQuery` is needed.

9. **Collapse the special states.** Take `State=Fin 1` in `OracleTM`, so `q₀=qQuery=qYes=qNo`. For every oracle the initial configuration is fixed by `step`: the ordinary transition is never consulted, even if it was defined to halt. More selectively, `qYes=qQuery` makes a positive response re-query the unchanged tape forever. This contradicts the unqualified claim that yes/no states execute ordinary transitions; it does not by itself demonstrate an enlargement of an oracle complexity class.

10. **Delimiter junk and the no-blank fallback.** Query tapes with cell 0=`some false`, cell 1 blank and arbitrary junk afterwards all submit `[false]`; clearing cell 0 submits `[]`. This is the declared delimiter convention. For an initialized run after t steps, every write occurred at a head position whose absolute value is at most t−1, so cell t is blank and
    \[
    \operatorname{length}(\mathrm{queryString}(M.\mathrm{runFrom}\ O\ (M.\mathrm{initCfg}\ x)\ t))\le t.
    \]
    Thus the blank-free fallback is not executable from initialization. An arbitrary raw configuration filled with bits at all nonnegative positions does map to `[]`, and this behavior must not be used as a model of a reachable finite query.

11. **k=0 and t=0 in the oracle embedding.** The added query tape is the sole tape when k=0 and is blank with head zero in both initial-configuration constructions. At t=0 both run expressions in the lockstep theorem are the same embedded configuration; a pre-halted configuration remains fixed at all later times. For a nonhalting embedded configuration every reachable state remains in the left summand until halt, so none of the right-summand transitions is used.

12. **Preserving versus automatically erasing the oracle tape.** For 0≤i<n, let
    \[
    u_{n,i}=1^i\,0\,1^{n-i-1},\qquad
    F^O(0^n)=\bigoplus_{i=0}^{n-1}\mathbf1[u_{n,i}\in O].
    \]
    A persistent-tape machine writes n ones once, moves a single zero through the word, queries each resulting word, and maintains the parity on a separate work cell, all in O(n) time. In the variant that blanks the whole query tape after each answer, any machine correct for every oracle must query all n distinct words on its run with the empty oracle: if it omits one, adding precisely that word to the oracle changes the required parity without changing any answer in the run. Each length-n query then requires n new symbol writes following the previous erasure, giving at least n² writing steps. Therefore there is no uniform constant-factor simulation in this direction. Polynomial overhead is sufficient for polynomial-time classes; that weaker statement does not justify the current constant-overhead claim.

## Polynomial-time normalization

The padded P definition has the intended content. For every natural n,d,
\[
n^d+1\le 2(n+1)^d,\qquad
(n+1)^d\le 2^d(n^d+1).
\]
For the second inequality, handle n=0 directly; for n≥1 use n+1≤2n. These inequalities show that the current P is exactly the class with a fixed finite machine and a bound C(n+1)^d; arbitrary polynomial upper bounds are absorbed in the same way. Degree zero contributes only constant time, already included in the degree-one component, and `DTIME (fun _ => 1)=DTIME (fun _ => 2)⊆P`.

This equivalence is to conventional polynomial time, not a literal unpadded expression evaluated on all natural lengths. For every d≥1, `DTIME (fun n => n^d)=∅` because of n=0; if d=0 is also included, that unpadded union becomes just `DTIME 1`. The existing +1 correction should remain and its characterization should be proved in Lean.

The other declared model variations are benign for these time classes after constant-factor simulations, but do not preserve exact step budgets. Finite alphabets have fixed-length block encodings; an extra work tape can simulate AB's read-write output tape before the final answer bit is emitted; an extra tape can track a simulated input head's excursion into the blank suffix while the real head stays clamped. Start-marker and bidirectional conventions likewise require a simulation argument, not an exact identification of the underlying machines. The selected Option/Boolean representation and singleton output do not by themselves furnish such proofs.

## Proposed machine-checkable sanity theorems

These are requested specifications, not claims of completed Lean proofs.

| Area | Statements to add |
|---|---|
| Halting and time | `¬ M.ComputesInTime x y 0`; equivalence of `ComputesInTime` with the halted-state/output conjunction; equivalence with existence of a first halting time ≤t producing y; oracle halting absorption. |
| Output | Initial-run output length ≤t; earlier output is a prefix of later output; a halted output is stable; singleton output excludes extra symbols. |
| DTIME | `(∃ n, T n=0) → DTIME T=∅`; positive-constant reformulation of `DTIME`; explicit one-state, zero-work-tape witnesses for the two constant languages when `∀ n, 1≤T n`. |
| Constructibility | For the current definition, prove `¬ TimeConstructible id`, `¬ TimeConstructible (fun n => n+1)` and `TimeConstructible (fun n => 2^n)`. For a repaired definition, prove identity constructibility including n=0, with a concrete linear-time binary counter construction. |
| Reachable oracle queries | In an initialized run after t steps, query-tape cell t is blank; the query length is at most t; changing cells after the first blank leaves the current query unchanged. |
| Oracle state discipline | A `WellFormed` predicate making query/yes/no pairwise distinct, or an injective designation `Fin 3 → State`; answer steps preserve all non-state fields. State which results need well-formedness and retain the legitimate `q₀=qQuery` case. |
| Oracle embedding/removal | Initial configurations commute with embedding; actions commute with embedding; no `Sum.inr` state is reachable from an embedded configuration. Add the converse empty-oracle simulation: replace a query transition by a stationary action entering `qNo`, yielding exact lockstep with an ordinary machine on k+1 tapes. |
| Polynomial time and PAL | Characterize P by C(n+1)^d bounds and by positive exponents in its existing padded union; prove `DTIME 1⊆P`. Implement the three-state palindrome witness, including its three-step accepting trace on empty input. |
| Finiteness and encodings | Preserve alphabet-finiteness hypotheses for general-symbol machine encodings; introduce a finite binary oracle bundle before defining oracle classes. Any theorem transferring the vendored encoding-relative computability predicate to ordinary binary computability must include an effective encoding conversion. |

For the intended constructibility repair, merely replacing T(n) by c·T(n) leaves T(0)=0 unusable. A concrete candidate is
\[
(\forall n,\ n\le T(n))\land
\exists c>0\ \exists M:\mathrm{FinTM\ Bool}\ \forall x,\quad
M.\mathrm{ComputesInTime}\,x\,(T(|x|)).\mathrm{bits}\,
\bigl(c\,(T(|x|)+1)\bigr).
\]
An explicitly eventual bound with separately handled small inputs is another option. Either change must be documented, and exact numerical constants in later results must be reconsidered rather than silently inherited from the strict definition.

## Findings table

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | **major** | `TimeConstructible.lean · TimeConstructible` and fallback discussion | The strict definition excludes the source's identity example; constant-factor slack alone does not fix all lengths. | Adversarial cases 5–6 prove failure for n and n+1 even on positive lengths. At length zero, c·0 still cannot halt. No false constructibility instance is currently asserted, so this is a definition/downstream-contract issue, not a refuted `sorry`. | Use c·(T(n)+1), or an eventual convention with explicit small-input handling; document the change and prove identity constructibility before using the intended examples downstream. |
| 2 | **major** | `Oracle.lean · OracleTM`, `step` | Designated special states may coincide, invalidating the advertised ordinary behavior of answer states. | With `qYes=qQuery` and a positive query, `step` keeps re-querying and ignores the ordinary transition. A one-element state type can make every initialized oracle run stationary. | Require query/yes/no pairwise distinctness at the faithful machine interface, or supply and use a well-formedness predicate. Do not prohibit `q₀=qQuery`. |
| 3 | **major** | `Oracle.lean · module Design` | The claim that preserving and clearing the query tape simulate each other with constant overhead is false for arbitrary oracles. | Case 12 gives O(n) versus Ω(n²) for parity of n distinct length-n queries when the tape is automatically cleared. | Replace the claim by polynomial-overhead equivalence for polynomial-time classes; give the simulation and do not transfer exact DTIME bounds using this sentence. |
| 4 | **minor** | `Configuration.lean · Action`, `Cfg.init`; `Finite.lean` source-fidelity descriptions | The layer is a model variation, not literally AB's §1.2 machine with the same step counts. The output variation is missing from the pack's declared-deviation list. | AB p. 12 gives a read-write output tape; the code can only append output. AB begins on start markers; the code begins at input position 1 with entirely blank work tapes. AB p. 19 explicitly lists write-only output as a variation. | Document these differences at the source-facing interface and add simulations with stated overhead before importing exact constants. Keep the model if desired. |
| 5 | **minor** | `Oracle.lean`, plan and audit pack · `[AB09, Definition 3.6]` | The oracle-definition citation is wrong for the supplied edition. | PDF p. 99/book p. 73 labels oracle machines Definition 3.4; 3.6 is an example. | Change these references to Definition 3.4, with the page or edition recorded. |
| 6 | **minor** | `Oracle.lean · ofMultiTapeTM` docstring | “Halts immediately from the fresh states” is false for the fresh query state. | From `some (Sum.inr 0)`, one step reaches `some (Sum.inr 1)` or `some (Sum.inr 2)`; the next step halts. Both lockstep theorems avoid this configuration and remain true. | Say the ordinary transition table halts from fresh states, while the query override first takes one answer step; or restrict the sentence to the two answer states. |
| 7 | **minor** | `P.lean · module introduction`, `mem_P_of_dtime_le` docstring | Two prose statements do not match the declarations. | The introduction uses the unpadded union; the theorem's docstring says eventual domination while its hypothesis is domination for every n. | State the padded union consistently. Say “pointwise,” or add a separate eventual-bound lemma absorbing the finitely many exceptions. |
| 8 | **minor** | `AroraBarakChapter1Plan.md · §§3.1–3.2` | The described bundle and sanity check overstate the delivered interface. | `FinTM` bundles state finiteness but not alphabet finiteness. The current lockstep theorems embed ordinary machines under any oracle; they do not eliminate an arbitrary empty-oracle machine. | Correct the bundle description and add the reverse empty-oracle construction described above. Require a finite bundle before exposing oracle complexity classes. |
| 9 | **note** | `Finite.lean · ComputesInTime`; `DTIME.lean · DecidesInTime`, `DTIME` | No halting-at-t or classical-indicator trivialization was found in these definitions. | Absorption gives an upper bound; initialization prevents zero-step decisions; singleton output rules out output garbage; the machine is chosen before all inputs; `Bool` and the state bundle make the transition table finite. | Add the corresponding sanity lemmas; keep these mathematical definitions. |
| 10 | **note** | `Oracle.lean · queryString`, `runFrom_ofMultiTapeTM`, `computesInTime_ofMultiTapeTM` | The no-blank fallback does not affect initialized computations, and the two embedding statements survive the boundary cases. | Cell t is blank after t initialized steps. The embedding preserves old fields, initializes the new tape correctly, and never reaches a right-summand state, including when k=0. | Prove the reachable-support/query-length invariants and the helper commutation lemmas. No change to the query extraction is required for this convention. |
| 11 | **note** | `P.lean · P`; `Examples.lean · PAL` and both theorems | The +1 normalization has the intended polynomial-time content, and the palindrome assertions admit finite-machine witnesses including empty input. | The two polynomial inequalities above establish the normalization; the explicit three-state construction uses at most 3(n+1) steps. | Keep the normalization and complete the individual proofs and empty-input sanity trace. |

Notation: M is a machine; O an oracle language; T a length-dependent time bound; x,y input/output words; n a word length; t,t′ step budgets; k the number of ordinary work tapes; a,c,C time constants; d a polynomial degree; b a bit; i,j cell or word indices; s a space count. The words 0ⁿ and 1ⁿ repeat the indicated bit n times; juxtaposition concatenates words. The word uₙ,ᵢ is the length-n word with its sole zero at position i, and Fᴼ is the displayed parity function. The symbol ⊕ in that formula is XOR, and **1**[condition] is its Boolean truth bit. `Sum.inl`/`Sum.inr`, `none`/`some`, `[]` and `.bits` retain their Lean meanings; `id` is the identity function. O(n) and Ω(n²) are asymptotic upper and lower bounds, respectively.
