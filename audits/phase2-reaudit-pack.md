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
