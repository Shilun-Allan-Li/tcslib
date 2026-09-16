# External audit pack — Phase 2 (robustness, composition, model invariance)

Audits the phase-2 skeleton at commit `2917a1b9` on `complexity/arora-barak-ch1`:
Claims 1.5/1.6/1.8, oblivious machines, composition combinators, and the class-level
model-invariance corollaries — all statement-first, 11 new `sorry`s (28 total), every
file elaborating with zero errors. Phase 1 closed its audit loop
(`audits/phase1-resolutions.md`); this pack opens phase 2's. Record findings in
`audits/phase2-findings.md`.

## Brief for the auditor

Same ground rules as the phase-1 rounds: you audit the trusted surface — definitions,
theorem statements, remaining `sorry`s, and declared deviations — not tactic scripts.
Failure modes: infidelity to [AB09], trivialization, unprovability as literally
stated, missing hypotheses. For every **new** definition and theorem (listed below):
restate it in your own mathematical English before reading its docstring, compare
against the cited [AB09] location, and report daylight. For every new `sorry`: argue
in 2-5 sentences why it is true as literally stated, or exhibit the problem. Attempt
at least **5 adversarial instantiations**. Do not give a blanket approval.

New surface under audit: `Turing.FinTM.ComputesFunInTimeVia` (added to `Finite.lean`);
all of `Composition.lean` (`computesFunInTime_id`, `computesFunInTime_const`,
`computesFunInTime_comp`); all of `Robustness/` (`alphabet_reduction`;
`one_work_tape`, `one_work_tape_binary`; `NonnegativeHeads`, `nonnegative_heads`;
`Oblivious`, `oblivious_of_mem_DTIME`); all of `ClassP/ModelInvariance.lean`
(`DecidesInTimeVia`, `mem_DTIME_of_decidesInTimeVia`, `mem_P_of_decidesInTimeVia_poly`,
`mem_P_iff_one_work_tape`). Everything else is unchanged since the closed phase-1
loop; spot-check rather than re-audit.

## Declared in-model renderings (the main audit target — judge their faithfulness)

Chapter 1's robustness claims are stated by [AB09] across *different machine models*;
our formalization has one model, so each claim is rendered inside it. These renderings
are decisions the audit should explicitly endorse or reject:

1. **Claim 1.5 (alphabet).** "Machine over finite `Γ` computing a binary function" is
   expressed via a symbol embedding (`ComputesFunInTimeVia e`, inputs `x.map e`,
   outputs `(f x).map e`), because our model has one alphabet for all tapes while
   [AB09] keeps input/output binary and reduces only the work alphabet. The simulator
   preserves the number of work tapes.
2. **Claim 1.6 (single tape).** Rendered as **one work tape** (`M'.k = 1`), keeping
   the structural read-only input and write-only output tapes. [AB09]'s merged
   input/work/output single-tape machine is a *different structure*, not an instance
   of `MultiTapeTM`, and is declared out of scope.
3. **Claim 1.8 (bidirectional).** Our tapes are already `ℤ`-indexed, so the rendering
   is: every machine is simulated by one whose work heads never visit negative cells
   (`NonnegativeHeads`), via [AB09]'s folding construction.
4. **Obliviousness.** Defined as: head positions at every time `t` agree across
   same-length inputs. Because halting freezes heads, this forces oblivious machines
   to halt at length-determined times — hence the `TimeConstructible` hypothesis in
   the Exercise 1.5 statement. Output-emission times are *not* constrained, only head
   positions, matching [AB09]'s wording.
5. **Convention obligations from phase 1, finding 4** (dispositions to assess):
   the append-only vs read-write output-tape simulation is discharged by
   `Composition.lean`'s buffer-and-flush construction plus documentation, on the
   stated ground that no exact step count is ever imported from [AB09] (every bound
   in the development carries an existential constant). The persistent-vs-erased
   query-tape polynomial-overhead statement is deferred to the Chapter 3 oracle-class
   work, where polynomial overhead is meaningful. Both decisions are recorded in the
   plan's decision log.

## Specific questions

1. `ComputesFunInTimeVia`: is anything lost relative to [AB09]'s formulation — e.g. a
   `Γ`-machine whose *input* uses symbols outside `e`'s range, or the fact that `e`
   need not hit [AB09]'s designated `{0,1} ⊆ Γ`? Is `∀ x : List α` over *all* binary
   strings the right quantifier for the corollaries drawn from it?
2. `alphabet_reduction`: verify the claim survives with `M'.k = M.k` (the block-code
   simulation needs no extra tape?), and that the emitted-symbols-in-range argument
   (append-only output equals the final output) is airtight — including inputs `x`
   where the machine emits *before* it could know the input.
3. `one_work_tape` / `one_work_tape_binary`: is the quadratic bound `c · (T n + 1)²`
   correct for the interleaved-with-marks layout ([AB09] says `5k T(n)²`), including
   the visited-zone-growth argument? Does the binary corollary's constant composition
   `c₂ · (c₁ · (T n + 1)² + 1) ≤ c · (T n + 1)²` hold for all `n` (note `T ≥ 0`,
   `(T n + 1)² ≥ 1`)?
4. `nonnegative_heads`: is `NonnegativeHeads` (initialized runs only) the right
   unidirectionality predicate, or should it constrain arbitrary configurations? Check
   the folding simulation preserves `k` and that a work head parked at `0` moving left
   (clamped in [AB09]'s unidirectional model, a real move in ours) causes no
   infidelity in this simulation direction.
5. `Oblivious`: does the definition have the intended extension — e.g. is the
   frozen-heads argument correct that oblivious machines halt at length-determined
   times, or can a machine halt at input-dependent times with coincidentally agreeing
   frozen positions and still be `Oblivious`? If the latter, does any planned use
   (Cook-Levin tableaux) need the stronger "halting time is a function of length"?
   Should the definition also fix the input-head position comparison at `t` beyond
   both halts?
6. `oblivious_of_mem_DTIME`: is the repaired (`c · (T n + 1)`-budget)
   `TimeConstructible` sufficient for the padding argument, and is the conclusion
   shape (`DecidesInTime` within `c · (T n + 1)²`) consistent with the sweep
   simulation that continues past the simulated machine's halt?
7. `computesFunInTime_comp`: is `Monotone T₂` the right hypothesis (vs monotone-on-a
   -tail, or replacing `T₂ (T₁ n)` by `sup`)? Is the bound shape
   `c · (T₁ n + T₂ (T₁ n) + 1)` achievable given the rewind of the intermediate tape
   and phase switching? Check the `|f x| ≤ T₁ |x|` step against `output_length_le`
   (length ≤ *halting time* ≤ budget).
8. The two convention dispositions in item 5 above: acceptable, or should either be a
   formal theorem in phase 2?
9. Adversarial instantiations to attempt: `T = fun _ => 0` through each robustness
   statement (bounds are padded — do any degenerate?); a `k = 0` machine through
   `one_work_tape` and `nonnegative_heads`; `f = id` and `g` constant through `comp`;
   an `Oblivious` machine that never halts (do the definitions admit it, and should
   they?); `Γ` a one-element type in `alphabet_reduction` (then `e : Bool ↪ Γ` cannot
   exist — is the theorem vacuous there, and is that fine?).

## Scope

| Item | Where |
|---|---|
| Files under audit | `TCSlib/Complexity/TuringMachine/{Finite,Composition}.lean`, `TCSlib/Complexity/TuringMachine/Robustness/*.lean`, `TCSlib/Complexity/ClassP/ModelInvariance.lean` (attached with all other sources for context) |
| Source text | Arora & Barak 2009, §1.3.1 (Claims 1.5, 1.6, 1.8; Remark 1.7; PDF pp. 42-45), §1.6.1 (PDF pp. 51-52), Exercise 1.5 (PDF p. 60) |
| Context | `AroraBarakChapter1Plan.md` (esp. decision log), `policy.md`; phase-1 records in `audits/` |
| Out of scope | tactic scripts; phase-1 surface (closed loop) beyond spot-checks; the vendored files |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.
