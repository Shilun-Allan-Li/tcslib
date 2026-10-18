# External audit pack — Phase 1, round 2 (re-audit of fixes)

Round 1 (`audits/phase1-findings.md`, attached) audited the phase-1 skeleton at commit
`65a3fe52` and returned 3 major and 5 minor findings plus a sanity-theorem menu. All
were accepted and resolved at commit `3a45aa2f`. This round audits **the fixes and the
newly added statements**. Phase 2 does not begin until this round returns no blockers
or majors. Record findings in `audits/phase1-reaudit-findings.md`.

All eight Lean sources are attached in full (every file elaborates with zero errors;
16 `sorry`s remain, each with a proof sketch).

## Resolution changelog (round-1 finding → change made)

| # | Finding (round 1) | Resolution |
|---|---|---|
| 1 | major — strict `TimeConstructible` excludes `id` | Definition repaired to `∃ c > 0, … within c·(T n + 1)` steps; refutation documented in the module docstring; `timeConstructible_id` added (sorry'd, binary-counter sketch). |
| 2 | major — oracle special states may coincide | `OracleTM.WellFormed` predicate added (pairwise-distinct `qQuery`/`qYes`/`qNo`; `q₀ = qQuery` allowed); `ofMultiTapeTM_wellFormed` **proved**; hazard documented on the structure and in the module docstring. |
| 3 | major — false constant-overhead claim for query-tape conventions | Docstring corrected to polynomial-overhead with the parity counterexample cited; exact-bound transfer explicitly forbidden. |
| 4 | minor — undeclared output/initialization deviations | Declared in `DTIME.lean` ("Design and deviations"): append-only output vs [AB09]'s read-write output tape (simulation = phase-2 obligation), no start markers, input head starts on first symbol. |
| 5 | minor — wrong citation (Definition 3.6) | All citations corrected to [AB09, Definition 3.4] in `Oracle.lean` and the plan. |
| 6 | minor — `ofMultiTapeTM` docstring wrong about `qQuery` | Reworded: the transition table halts from fresh states; the query override fires first from `qQuery` (its table row is dead code). |
| 7 | minor — P.lean prose mismatches | Module intro now states the padded union and why; `mem_P_of_dtime_le` docstring says pointwise, with the eventual variant explicitly deferred. |
| 8 | minor — plan overstates `FinTM` bundle and oracle sanity | Plan §3.2 corrected (state finiteness only; alphabet is a parameter; finite oracle bundle deferred to Ch. 3); §3.1 now describes both directions; converse `plainEmptyOracle` + `runFrom_plainEmptyOracle` added. |
| 9-11 | notes — sanity menu | Curated subset added (below); the full menu remains recorded in round-1 findings for the fill phase. |

New statements added this round (the audit targets): `MultiTapeTM.output_length_le`,
`MultiTapeTM.output_prefix`, `FinTM.not_computesInTime_zero` (**proved**),
`OracleTM.WellFormed`, `OracleTM.ofMultiTapeTM_wellFormed` (**proved**),
`OracleTM.queryString_length_le`, `OracleTM.plainEmptyOracle`,
`OracleTM.runFrom_plainEmptyOracle`, `DTIME_eq_empty_of_exists_zero`, `mem_P_iff`,
`dtime_one_subset_P`, `timeConstructible_id`, and the repaired `TimeConstructible`.

## Brief for the auditor

Same ground rules as round 1: you audit the trusted surface (definitions, theorem
statements, remaining `sorry`s), not tactic scripts. Failure modes: infidelity,
trivialization, unprovability, missing hypotheses. Do not give a blanket approval; an
empty findings table must be justified by the restatements.

This round's tasks, in priority order:

1. **Verify each round-1 resolution**: for every row of the changelog, check the change
   actually resolves the finding and introduces no new defect.
2. **Blind-restate the changed and new declarations** (the list above plus
   `TimeConstructible`): restate in your own mathematical English before reading the
   docstring, compare against [AB09] and against round 1's intent.
3. **Disposition every new `sorry`** (argue true as stated in 2-5 sentences, or exhibit
   the problem). The eight round-1 sorries were already confirmed and are textually
   unchanged — spot-check that they are indeed unchanged rather than redoing them.
4. **Sweep the corrected prose** (docstrings, deviation lists, plan §§3.1-3.2) for
   remaining inaccuracy.

## Specific questions for this round

1. `TimeConstructible` (repaired): does `c · (T n + 1)` genuinely admit `id` in *this*
   model — check the binary-counter sketch against the append-only, in-order output
   tape (bits must be emitted least-significant-first; `Nat.bits 0 = []`). Is anything
   in Chapter 1's downstream use (timed universal machine) still blocked by this form?
2. `OracleTM.WellFormed`: is pairwise distinctness the right condition — in particular,
   is `qYes ≠ qNo` genuinely necessary for the faithful interface, or over-strong
   (both are ordinary table states)? Would any planned result break if `qYes = qNo`?
3. `plainEmptyOracle` / `runFrom_plainEmptyOracle`: is *exact* lockstep literally true?
   Verify that `Action.apply` of the stationary action `⟨0, no write/no move, no
   output, some qNo⟩` is the identity on every configuration field except the state
   (input-head clamp at boundaries included), and that it matches the oracle answer
   step exactly.
4. `queryString_length_le`: check the `t = 0` boundary and whether the "writes stay
   within radius `t - 1`" invariant is correctly stated for heads that may move before
   writing.
5. `mem_P_iff`: verify both directions' constant arithmetic
   (`a · (n^c + 1) ≤ 2a · (n+1)^c` and `(n+1)^d ≤ 2^d · (n^d + 1)`), including `n = 0`
   and `d = 0`.
6. `output_prefix` is stated from an *arbitrary* configuration while `output_length_le`
   is stated from the initial one — is each the right generality?
7. Are there degenerate instantiations of the new definitions we missed (e.g.
   `WellFormed` for `State = Fin 2`; `plainEmptyOracle` of a machine whose `qNo` is
   also `qQuery` — note `WellFormed` is *not* a hypothesis of the lockstep theorem: is
   it needed there, or does the theorem hold degenerately too?).

## Scope

| Item | Where |
|---|---|
| Lean files under audit | the eight files attached (emphasis on `TimeConstructible.lean`, `Oracle.lean`, `Finite.lean`, `DTIME.lean`, `P.lean`; `Configuration.lean`, `Deterministic.lean`, `Examples.lean` unchanged since round 1 except round-1's tactic repairs in `Configuration.lean`) |
| Source text | Arora & Barak 2009, Chapter 1 (PDF pp. 35-63) and §3.4 (Definition 3.4, PDF p. 99) |
| Context | round-1 findings (attached), updated `AroraBarakChapter1Plan.md`, `policy.md` |
| Out of scope | tactic scripts; the vendored files' upstream design |

## Declared deviations (updated after round 1 — verify completeness)

* Tape alphabet `Option Symbol`, blank = `none`; classes fix `Symbol := Bool`;
  bidirectional tapes, no start symbol; input head starts on the first symbol; single
  halting state with accept/reject by output.
* **Append-only output tape** (vs [AB09]'s read-write output tape) — declared, with the
  constant-overhead simulation a phase-2 obligation.
* Input head clamped to one cell beyond the input.
* `DTIME` constant over all `c : ℕ` (`c = 0` unsatisfiable); `P` padded with `+ 1`.
* `TimeConstructible` uses `Nat.bits` (little-endian) and the `c · (T n + 1)` budget
  (audit-mandated deviation from the literal text).
* Oracle: query = query-tape cells from 0 to first blank (`[]` on the unreachable
  no-blank branch); answer step changes only the state; persistent (non-erased) query
  tape; `WellFormed` required at the faithful interface only.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.

---

# ATTACHMENT A — Round-1 findings (context for verifying resolutions)

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
| §1.2 | k-tape TM `(Γ, Q, δ)`: read-only input tape, work tapes, write-only output tape; start configuration; halting; Example 1.1 (palindromes in 3n steps) | Yes |
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
  Apache-2.0) has an Arora-Barak-faithful `MultiTapeTM`: read-only input tape, k work
  tapes, write-only output tape, explicit time and space semantics, a nondeterministic
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
  Examples.lean           -- PAL ∈ DTIME(3n) [AB09, Ex 1.1]; selected Ex 1.14
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
   the simulation vocabulary everything later reuses. Scope now explicitly includes the
   simulation obligations recorded by the phase-1 audit: append-only vs read-write
   output tape (constant overhead), start-marker/initialization conventions, and
   persistent vs auto-erased oracle query tape (polynomial overhead only — a
   constant-overhead simulation is provably impossible; findings 3-4).
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

# ATTACHMENT C — Lean sources under audit

## ===== TCSlib/Complexity/TuringMachine/Configuration.lean =====

```lean
/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Aviv Bar Natan

Vendored from cslib (https://github.com/leanprover/cslib), file
`Cslib/Computability/Machines/Turing/MultiTape/Configuration.lean`,
at commit a374775894efb9b7196cccf11235c60a97086dc1 (2026-09-14).
Local modifications (see policy.md §2, vendored code):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* remapped `Mathlib.Basic.Sign.Defs` to its location at our mathlib pin,
  `Mathlib.Data.Sign.Defs`; dropped the cslib-internal `Cslib.Init` import;
* added the repository-standard `set_option` header.
The mathematical content is unchanged.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Data.Sign.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Configurations of Multi-Tape Turing Machines

Configurations of a multi-tape Turing machine with a read-only input tape, `k` work tapes and one
write-only output tape, together with what a single transition does to one and the space measure
read off a list of them.

## Design

Nothing here mentions a machine. A step is described in two parts: an `Action`, recording
which way the input head moves, what is written and where the work heads move, which symbol is
emitted and which state follows; and `Action.apply`, which carries it out on a
configuration.

The output tape is part of the configuration, so the string emitted along a run can be read off
the configuration the run ends in.

## Main definitions

* `Cfg`: the configuration: the internal state, the tape contents and head positions, and the
    output tape
* `Action`: what a machine does in one step
* `Action.apply`: the effect of one action on a configuration
* `Cfg.Halted`, `Cfg.init`: halting, and the configuration a machine starts in
* `spaceUsedOfCfgs`: work tape cells touched along a list of configurations

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the k-tape Turing machine.)
* [Pap94] C. Papadimitriou, *Computational Complexity*, Addison-Wesley, 1994.
  (§2.3, §2.5: the machine model and the space measure.)
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/-- What a machine does in one step. -/
structure Action (k : ℕ) (Symbol State : Type*) where
  /-- The movement (attempt) of the input head. -/
  inputTape : SignType
  /-- Actions on the work tapes: optionally a symbol to write and the head movement. -/
  workTapes : Fin k → (Option (Option Symbol)) × SignType
  /-- An optional symbol to output. -/
  output : Option Symbol
  /-- The successor state or none to halt. -/
  state : Option State

/--
The configurations of a Turing machine is relative to the input of the machine and consist of:
- an `Option`al state (or none for the halting state),
- the position of the input head (shifted by one),
- the contents of the work tape,
- the positions of the work tape heads,
- the contents of the write-only output tape
-/
@[ext]
structure Cfg (k : ℕ) (Symbol State : Type*) (input : List Symbol) where
  /-- the state of the TM (or none for the halting state) -/
  state : Option State
  /-- the position of the input head, shifted by one -/
  inputPos : Fin (input.length + 2)
  /-- the work tapes -/
  workTapes : Fin k → ℤ → Option Symbol
  /-- the positions of the heads on the work tapes -/
  workTapePos : Fin k → ℤ
  /-- the contents of the write-only output tape -/
  output : List Symbol
deriving Inhabited

/-- Two configurations of a machine without work tapes are equal if their states, input head
positions and outputs are equal. -/
lemma Cfg.ext_zero_tapes {Symbol State : Type*} {input : List Symbol}
    {cfg₁ cfg₂ : Cfg 0 Symbol State input} (state : cfg₁.state = cfg₂.state)
    (inputPos : cfg₁.inputPos = cfg₂.inputPos) (output : cfg₁.output = cfg₂.output) :
    cfg₁ = cfg₂ :=
  Cfg.ext state inputPos (funext fun i => i.elim0) (funext fun i => i.elim0) output

/-- Attempt to move the input tape head.
The machine can only read one empty cell outside of the input,
any attempted movement beyond that results in no movement.

The addition is performed in `ℤ` before clamping. Performing it in `Fin (n + 2)` would wrap an
outward boundary move to the opposite end of the input. -/
@[scoped grind =]
def moveInputPos {n : ℕ} (pos : Fin (n + 2)) (m : SignType) : Fin (n + 2) :=
  let p := ((pos.val : ℤ) + (m.cast : ℤ)).toNat
  if h : p < n + 2 then ⟨p, h⟩ else ⟨n + 1, by omega⟩

@[simp]
lemma moveInputPos_zero {n : ℕ} (pos : Fin (n + 2)) :
    moveInputPos pos 0 = pos := by
  apply Fin.ext
  simp [moveInputPos, pos.isLt]

@[simp]
lemma moveInputPos_leftBoundary {n : ℕ} :
    moveInputPos (0 : Fin (n + 2)) (-1) = 0 := by
  apply Fin.ext
  simp [moveInputPos]

@[simp]
lemma moveInputPos_rightBoundary {n : ℕ} :
    moveInputPos (⟨n + 1, by omega⟩ : Fin (n + 2)) 1 = ⟨n + 1, by omega⟩ := by
  -- ported proof: `dite_eq_right` does not exist at our mathlib pin
  apply Fin.ext
  simp only [moveInputPos, SignType.coe_one]
  split <;> simp <;> omega

/-- A left move away from the left input boundary decrements the native input position. -/
lemma moveInputPos_neg_of_ne_left {n : ℕ} (p : Fin (n + 2)) (h : p ≠ 0) :
    moveInputPos p .neg = ⟨p.val - 1, by have := p.isLt; omega⟩ := by
  -- ported proof: `dite_eq_left` does not exist at our mathlib pin
  have hlt := p.isLt
  apply Fin.ext
  simp only [moveInputPos, SignType.neg_eq_neg_one, SignType.coe_neg_one]
  split <;> simp <;> omega

/-- A right move away from the right input boundary increments the native input position. -/
lemma moveInputPos_pos_of_ne_right {n : ℕ} (p : Fin (n + 2)) (h : p.val ≠ n + 1) :
    moveInputPos p .pos = ⟨p.val + 1, by have := p.isLt; omega⟩ := by
  -- ported proof: `dite_eq_left` does not exist at our mathlib pin
  have hlt := p.isLt
  apply Fin.ext
  simp only [moveInputPos, SignType.pos_eq_one, SignType.coe_one]
  split <;> simp <;> omega

/-- The symbol currently under the input tape head. -/
def Cfg.inputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  if h₁ : cfg.inputPos = 0 then none
  else if h₂ : cfg.inputPos = input.length + 1 then none
  else input[cfg.inputPos.val - 1]'(by
    -- ported proof: `grind` at our pin does not bridge the `Fin` equality with `.val`
    have h0 : (cfg.inputPos : ℕ) ≠ 0 := fun hv => h₁ (Fin.val_eq_zero_iff.mp hv)
    have hlt := cfg.inputPos.isLt
    omega)

@[simp]
lemma inputSymbolInner {cfg : Cfg k Symbol State input} (p : ℕ)
    (h₁ : cfg.inputPos.val = 1 + p)
    (h₂ : p < input.length) :
    cfg.inputSymbol = some input[p] := by
  -- ported proof: `grind` at our pin does not bridge the `Fin` equality with `.val`
  have h0 : ¬cfg.inputPos = 0 := fun hz => by
    rw [hz] at h₁
    simp at h₁
    omega
  have hL : ¬(cfg.inputPos : ℕ) = input.length + 1 := by omega
  simp only [Cfg.inputSymbol, dif_neg h0, dif_neg hL]
  simp only [show (cfg.inputPos : ℕ) - 1 = p from by omega]

/-- The symbol read by work tape `i`. -/
def Cfg.workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) : Option Symbol :=
  cfg.workTapes i (cfg.workTapePos i)

/-- A configuration is halted when it has no state to continue from. -/
abbrev Cfg.Halted (cfg : Cfg k Symbol State input) : Prop := cfg.state = none

/-- The initial configuration for a starting state and an input string. -/
@[simp]
def Cfg.init (q₀ : State) (input : List Symbol) : Cfg k Symbol State input :=
  ⟨some q₀, 1, fun _ _ => none, fun _ => 0, []⟩

/--
The effect of an action on a configuration: move the input head, write and move on the work tapes,
append the emitted symbol to the output tape, and go to the successor state. This is the part of a
step that does not depend on how the action was chosen.
-/
@[simp]
def Action.apply (action : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    Cfg k Symbol State input where
  state := action.state
  inputPos := moveInputPos cfg.inputPos action.inputTape
  workTapes i := match (action.workTapes i).1 with
    | none => cfg.workTapes i
    | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
  workTapePos i := cfg.workTapePos i + (action.workTapes i).2
  output := cfg.output ++ action.output.toList

/-- A work tape head moves by at most one cell when an action is applied. -/
lemma workTapePos_apply_le (action : Action k Symbol State)
    (cfg : Cfg k Symbol State input) (i : Fin k) :
    |(action.apply cfg).workTapePos i - cfg.workTapePos i| ≤ 1 := by
  simp only [Action.apply, add_sub_cancel_left, abs_le, SignType.cast]
  grind

/-- The work tape cells visited by the head of tape `i` along a list of configurations. -/
def visitedOfCfgs (cfgs : List (Cfg k Symbol State input)) (i : Fin k) : Finset ℤ :=
  (cfgs.map (·.workTapePos i)).toFinset

/-- The number of work tape cells touched by the heads along a list of configurations. -/
def spaceUsedOfCfgs (cfgs : List (Cfg k Symbol State input)) : ℕ :=
  ∑ i, (visitedOfCfgs cfgs i).card

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Deterministic.lean =====

```lean
/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger

Vendored from cslib (https://github.com/leanprover/cslib), file
`Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean`,
at commit a374775894efb9b7196cccf11235c60a97086dc1 (2026-09-14).
Local modifications (see policy.md §2, vendored code):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* remapped `Mathlib.Basic.Sign.Defs` to `Mathlib.Data.Sign.Defs` (its location at our mathlib
  pin); dropped the cslib-internal `Cslib.Init` import; added
  `Mathlib.Logic.Embedding.Basic` explicitly (upstream receives it transitively);
* dropped the relational semantics (`TransitionRelation`,
  `relatesInSteps_iff_runFrom_eq`) because it depends on the cslib-internal
  `Cslib.Foundations.Data.RelatesInSteps`; the iterated-step semantics `runFrom` is
  self-contained and suffices for the Chapter 1 development. Re-add it (or migrate to
  upstream cslib) when the step-indexed relational view is needed, e.g. for
  nondeterministic machines;
* added the repository-standard `set_option` header.
The remaining mathematical content is unchanged.
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Embedding.Basic
import TCSlib.Complexity.TuringMachine.Configuration

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic Multi-Tape Turing Machines

Defines deterministic Turing machines with a read-only input tape, `k` work tapes and one
write-only output tape.
The tapes contain symbols from `Option Symbol` for a finite alphabet `Symbol` (where `none` is the
blank symbol).

## Design

The multi-tape Turing machine uses a read-only input tape, `k` work tapes and a write-only output
tape.
The input head can move freely on the input, but any move attempt beyond one cell outside the input
results in no movement.
The transition function can optionally output one symbol, which models the write-only output tape.
Because of these restrictions, we ignore the input and output tapes for space usage of the machine.
The space usage is defined as the total number of cells the work tape heads visited during
execution.

Restricting the movement of the input head is not essential, but useful because it allows
us to easily bound the number of possible configurations of a space-bounded machine. Most textbooks
have this restriction.

Instead of considering the cells _visited_ by the work tape heads, some textbooks
(including [AB09]) only consider the number of cells that contain
a non-blank symbol at some point in the execution or the number of cells written to. This allows
work tape heads to freely move at no cost as long as they do not write. It is
important to note that this causes `DSPACE(1)` to include `DSPACE(log log n)`, a class that
contains e.g. the non-regular language `{0^n 1^n | n ∈ ℕ}` (it is accepted by a TM that writes a
single marker on the work tape and then counts the number of symbols by work tape head movement
without writing).
Defining space usage via "cells visited" thus yields the more fine-grained "complexity world" in
which `DSPACE(1)` is exactly the class of regular languages.

This definition is adapted from the one in [Pap94], chapter 2.3 including
the sub-linear space modifications from chapter 2.5 with the following changes:
- We allow Turing machines to choose to not write on a tape. This is equivalent to
  writing the read symbol again but makes it easier to reason about the semantics.
- Our tapes are infinite in both directions instead of just to the right. This definition is
  equivalent (see [AB09], Claim 1.8). It saves us from having to add a "start marker" to
  the alphabet.
- We only have a single halting state. The different ways to halt (accepting, rejecting, etc) can
  be distinguished based on the output.
- The way to prevent the input head to move outside the input is enforced by the interpretation
  and not by a restriction on the transition function. The two definitions are equivalent, but
  not restricting the transition function makes it easier to define a universal machine.

## Main definitions

We define a number of structures and concepts related to multi-tape Turing machine computation:

* `MultiTapeTM`: the TM itself
* `MultiTapeTM.runFrom`: the configuration reached after a given number of execution steps
* `spaceUsed`: the number of work tape cells touched by the heads until a certain step,
    our main space measure
* `ComputesInTimeAndSpace`: a proof that a specific TM computes an output from an input in a certain
    number of steps and using a certain number of tape cells
* `ComputesFunInTimeAndSpace`: a machine computes a function between specified encodings,
    respecting time and space bounds on each actual input.
* `ComputableInTimeAndSpace`: such a machine exists with binary alphabet and finitely many states.
* `ComputableInTimeAndSpaceOfLength`: the specialization to bounds on encoded input length.
* `DecidableInTimeAndSpace`: a proof that a TM decides a language within a certain time
    and space bound.

## References

* [Pap94] C. Papadimitriou, *Computational Complexity*, Addison-Wesley, 1994.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013.
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/--
A multi-tape Turing machine with `k` work tapes over the alphabet of `Option Symbol` (where `none`
is the blank tape symbol). Note that it is not required that `Symbol` or `State` are finite
to keep the definition more general. The restriction will be introduced once we start talking about
computability by Turing machines in general.
-/
structure MultiTapeTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- transition function, mapping a state, the current input symbol and a tuple of work head
  symbols to a movement for the input head, actions on the work tape, optionally a symbol to output
  and the successor state -/
  tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    Action k Symbol State

namespace MultiTapeTM

variable {input : List Symbol} {tm : MultiTapeTM k Symbol State}

section Cfg

/-!
## Stepping a Turing Machine

This section defines the step function that lets the machine transition from one configuration to
the next, and the configuration reached after a number of steps. Configurations themselves are
defined in `TCSlib.Complexity.TuringMachine.Configuration`.
-/

/-- The step function corresponding to a `MultiTapeTM`. -/
def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  -- in the halting state, we stay at the configuration
  | none => cfg
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The symbol (optionally) output when executing one step starting from configuration `cfg`. -/
def outputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  match cfg.state with
  | none => none
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).output

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (input : List Symbol) : Cfg k Symbol State input := Cfg.init tm.q₀ input

@[simp]
lemma step_of_halt {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg := by
  unfold step
  rw [h]

/-- The configuration reached by running the Turing machine for `t` steps from `cfg`.
If the Turing machine halts, it will stay at the halting configuration. -/
def runFrom (cfg : Cfg k Symbol State input) (t : ℕ) : Cfg k Symbol State input := tm.step^[t] cfg

@[simp]
lemma runFrom_zero {cfg : Cfg k Symbol State input} :
    tm.runFrom cfg 0 = cfg := by
  simp [runFrom]

lemma runFrom_succ_eq_step {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.runFrom (tm.step cfg) t := by
  simp [runFrom, Function.iterate_succ_apply]

lemma runFrom_succ_eq_step' {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.step (tm.runFrom cfg t) := by
  simp [runFrom, Function.iterate_succ_apply']

/-- Running `a + b` steps equals running `b` steps from the configuration reached after `a`. -/
lemma runFrom_add (cfg : Cfg k Symbol State input) (a b : ℕ) :
    tm.runFrom cfg (a + b) = tm.runFrom (tm.runFrom cfg a) b := by
  unfold runFrom
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- If a function `f` that maps the configurations of one TM to those of another one commutes with
their `step` function, then it also commutes with their `runFrom` function. -/
lemma runFrom_comm_of_step {k' : ℕ} {State' : Type*} {input input' : List Symbol}
    {tm : MultiTapeTM k Symbol State} {tm' : MultiTapeTM k' Symbol State'}
    (f : Cfg k Symbol State input → Cfg k' Symbol State' input')
    (hstep : ∀ cfg, tm'.step (f cfg) = f (tm.step cfg))
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    tm'.runFrom (f cfg) n = f (tm.runFrom cfg n) :=
  (Function.Semiconj.iterate_right (fun c => (hstep c).symm) n cfg).symm

/-- Running from a halting configuration stays at that configuration. -/
@[simp]
lemma runFrom_of_halt (cfg : Cfg k Symbol State input) (h : cfg.state = none) {n : ℕ} :
    tm.runFrom cfg n = cfg :=
  Function.iterate_fixed (step_of_halt h) n

@[simp]
lemma outputSymbol_of_halt {cfg : Cfg k Symbol State input} (h_halt : cfg.state = none) :
    tm.outputSymbol cfg = none := by
  simp [outputSymbol, h_halt]

/-- The work-tape head moves by at most one cell in a single step. -/
lemma workTapePos_step_le (c : Cfg k Symbol State input) (i : Fin k) :
    |(tm.step c).workTapePos i - c.workTapePos i| ≤ 1 := by
  unfold step
  cases hstate : c.state with
  | none => simp
  | some q => exact workTapePos_apply_le _ c i

end Cfg

section Space
/-! Now we define space usage and add some helper lemmas. -/

/-- The set of positions visited by the head of work tape `i` in the computation starting from
configuration `cfg` up to step `t`. -/
def visitedByTapeHead (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : Finset ℤ :=
  (Finset.range (t + 1)).image fun t' => (tm.runFrom cfg t').workTapePos i

/--
The number of work tape cells touched by the head of tape `i` in the computation starting from
configuration `cfg` up to step `t`.
-/
def spaceUsedByTape (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : ℕ :=
  (tm.visitedByTapeHead cfg t i).card

/--
The number of work tape cells touched by a computation starting from configuration
`cfg` up to step `t`.
-/
def spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) : ℕ := ∑ i, tm.spaceUsedByTape cfg t i

/-- A zero-tape Turing machine uses zero space. -/
@[simp]
lemma spaceUsed_zero_tapes_eq_zero (cfg : Cfg k Symbol State input) (t : ℕ) (h_zero : k = 0) :
    tm.spaceUsed cfg t = 0 := by
  unfold spaceUsed
  subst h_zero
  simp

/-- Each tape's space usage is bounded by the total space used. -/
lemma spaceUsedByTape_le_spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    tm.spaceUsedByTape cfg t i ≤ tm.spaceUsed cfg t :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- The space used up to step `t` is the space touched by the configurations up to step `t`. -/
lemma spaceUsed_eq_spaceUsedOfCfgs (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t = spaceUsedOfCfgs ((List.range (t + 1)).map (tm.runFrom cfg)) := by
  unfold spaceUsed spaceUsedByTape spaceUsedOfCfgs
  refine Finset.sum_congr rfl fun i _ => congrArg Finset.card ?_
  ext z
  simp [visitedByTapeHead, visitedOfCfgs]

end Space

open Cfg

/-- One step appends the symbol (optionally) emitted by that step to the output tape. -/
@[simp]
lemma step_output (cfg : Cfg k Symbol State input) :
    (tm.step cfg).output = cfg.output ++ (tm.outputSymbol cfg).toList := by
  unfold step outputSymbol Action.apply
  cases cfg.state <;> simp

/-- The output does not change after the machine has halted. -/
lemma runFrom_output_eq_of_halt
    (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    (tm.runFrom cfg t).output = (tm.runFrom cfg τ).output := by
  conv_lhs => rw [← Nat.sub_add_cancel hle, Nat.add_comm]
  rw [runFrom_add, runFrom_of_halt _ hhalt]

/-- A proof that the Turing machine `tm` on input `input` outputs `output` in at most `t` steps
and uses exactly `s` space.
Note that this does not require the alphabet or state set to be finite. -/
def ComputesInTimeAndSpace
    (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol)
    (t s : ℕ) : Prop :=
  (tm.runFrom (tm.initCfg input) t).state = none ∧
  (tm.runFrom (tm.initCfg input) t).output = output ∧
  tm.spaceUsed (tm.initCfg input) t = s

/-- A machine computes `f` between the supplied encodings, with bounds depending on the input.
The machine's alphabet and state type need not be finite. -/
def ComputesFunInTimeAndSpace {α β : Type*}
    (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol)
    (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, ∃ t' ≤ t a, ∃ s' ≤ s a,
    ComputesInTimeAndSpace tm (encIn a) (encOut (f a)) t' s'

/-- A function is computable within the input-indexed bounds by a machine with binary alphabet
and finitely many states. -/
def ComputableInTimeAndSpace {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    ComputesFunInTimeAndSpace tm encIn encOut f t s

/-- There exists a binary Turing machine with finitely many states that, for every input `a`,
computes `encOut (f a)` from `encIn a` in at most `t (encIn a).length` steps,
using at most `s (encIn a).length` work-tape cells. -/
abbrev ComputableInTimeAndSpaceOfLength {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : ℕ → ℕ) : Prop :=
  ComputableInTimeAndSpace f encIn encOut
    (fun a => t (encIn a).length) (fun a => s (encIn a).length)

/-- Resource bounds can be weakened independently on every input. -/
theorem ComputesFunInTimeAndSpace.mono {α β : Type*}
    {tm : MultiTapeTM k Symbol State} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s t' s' : α → ℕ}
    (h : ComputesFunInTimeAndSpace tm encIn encOut f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputesFunInTimeAndSpace tm encIn encOut f t' s' := fun a => by
  obtain ⟨u, hu, v, hv, hc⟩ := h a
  exact ⟨u, hu.trans (ht a), v, hv.trans (hs a), hc⟩

/-- Computability is monotone in the resource bounds. -/
theorem ComputableInTimeAndSpace.mono {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s t' s' : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableInTimeAndSpace f encIn encOut t' s' := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm, htm.mono ht hs⟩

open Classical in
/-- The Boolean indicator function of a set. -/
noncomputable def indicator {α : Type*} (L : Set α) : α → Bool :=
  fun x => if x ∈ L then true else false

/-- A set is decidable within the given input-indexed bounds when its Boolean indicator is. -/
def DecidableInTimeAndSpace {α : Type*} (L : Set α) (enc : α ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ComputableInTimeAndSpace (indicator L) enc ⟨fun b => [b], by intro a b h; simpa using h⟩ t s

/-- The Turing machine `tm` halts after exactly `t` steps on input `input`
if its state is `none` at step `t` and non-none at step `t - 1`.
Note that every Turing machine hast to perform at least one step to halt. -/
def haltsAtStep (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) : Bool :=
  (tm.runFrom (tm.initCfg input) t).state.isNone &&
  !(tm.runFrom (tm.initCfg input) (t - 1)).state.isNone

/-- If a Turing machine halts, the time step is uniquely determined. -/
lemma halting_step_unique
    {tm : MultiTapeTM k Symbol State}
    {input : List Symbol}
    {t₁ t₂ : ℕ}
    (h_halts₁ : tm.haltsAtStep input t₁)
    (h_halts₂ : tm.haltsAtStep input t₂) :
    t₁ = t₂ := by
  wlog h : t₁ ≤ t₂
  · exact (this h_halts₂ h_halts₁ (Nat.le_of_not_le h)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  cases d with
  | zero => rfl
  | succ d =>
    have halts₁ : (tm.runFrom (tm.initCfg input) t₁).state = none := by
      simp [haltsAtStep] at h_halts₁
      exact h_halts₁.left
    have halts₂ : (tm.runFrom (tm.initCfg input) (d + t₁)).state ≠ none := by
      grind [haltsAtStep, runFrom]
    refine absurd ?_ halts₂
    rw [Nat.add_comm, runFrom_add, tm.runFrom_of_halt _ halts₁]
    exact halts₁

/-- If a deterministic machine repeats a non-halting configuration, it never halts,
because the sequence between the two configurations will loop forever.
Note that this can be applied to two arbitrary and different time steps `t` and `t + Δ`
using `tm.runFrom_add`. -/
lemma not_halts_of_repeat_nonhalt
    (cfg : Cfg k Symbol State input)
    (h_not_halt : cfg.state ≠ none)
    (t : ℕ)
    (heq : tm.runFrom cfg (t + 1) = cfg) :
    ∀ t', (tm.runFrom cfg t').state ≠ none := by
  intro t'
  -- The configuration will repeat every `t + 1` steps.
  have hloop : ∀ n, tm.runFrom cfg (n * (t + 1)) = cfg := by
    intro n
    unfold runFrom
    rw [Nat.mul_comm, Function.iterate_mul]
    exact Function.iterate_fixed heq n
  by_contra hnh
  -- Assuming the machine halts at step `t'`, it is also halted at step `t' * (t + 1)`
  have h₁ : (tm.runFrom cfg (t' * (t + 1))).state = none := by
    have hle : t' ≤ t' * (t + 1) := by grind
    obtain ⟨tΔ , htΔ⟩ := Nat.exists_eq_add_of_le hle
    rw [htΔ, tm.runFrom_add]
    simp [hnh]
  simp [hloop t', h_not_halt] at h₁

end MultiTapeTM

end Turing
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
state type. This is the machine of [AB09, §1.2]: the raw `MultiTapeTM` is internal
plumbing, and every headline complexity-theoretic definition is stated over `FinTM`.

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
  which the raw structure does not enforce (e.g. `qYes = qQuery` would re-query
  forever): results at the faithful interface assume `OracleTM.WellFormed`. Note that
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
  steps has length at most `t` (so the no-blank fallback in `queryString` is
  unreachable from initialization).

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
(with degenerate behavior, e.g. `qYes = qQuery` re-queries forever), and the faithful
interface imposes `OracleTM.WellFormed`. [AB09, Definition 3.4] -/
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
pairwise distinct. Without this, the advertised semantics degenerates (`qYes = qQuery`
re-queries the unchanged tape forever; with all three collapsed the transition function
is never consulted). This is the standing hypothesis of the faithful oracle interface —
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
on every input `x`, the binary representation of `T |x|` within `T |x|` steps.
[AB09, §1.3] Time constructibility rules out pathological time bounds; it is the standing
hypothesis of the timed universal machine (phase 3) and, later, of the hierarchy theorems.

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
  prefix argument. We therefore allow a positive constant factor on `T n + 1`, which is
  sufficient for every downstream use (the timed universal machine, and later the
  hierarchy theorems) and restores the book's examples. Exact constants in downstream
  results must be derived from this form, not inherited from the strict reading.

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
the literal unpadded union is empty degree by degree in this model, since `n^c`
vanishes at `n = 0` and no machine halts in zero steps.]

## Design and deviations from [AB09]

* We take the union of `DTIME (fun n => n ^ c + 1)` over all `c : ℕ` where [AB09] writes
  `⋃_{c ≥ 1} DTIME(n^c)`. The `+ 1` repairs the empty-input degeneracy: a machine needs
  at least one step to halt, so no language whatsoever is decided within `c · 0^d = 0`
  steps on the empty input, and the literal [AB09] definition would (vacuously) exclude
  even constant-time machines on that input. For `n ≥ 1` the bounds `c · (n^d + 1)` and
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
eventual, domination: an eventual-bound variant absorbing finitely many exceptional
lengths requires patching the machine and is deferred.)

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
