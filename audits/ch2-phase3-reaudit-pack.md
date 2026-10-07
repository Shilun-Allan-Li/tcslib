# External audit pack — Chapter 2, Phase 3, round 2 (re-audit)

Audits commit `8b09a184` on `complexity/arora-barak-ch1`. Round 1
(`audits/ch2-phase3-findings.md`, audited at `1a7554d1`) reported **2
blockers, 1 major, 2 minors, 3 notes**: the blockers shared one obstruction —
`Turing.EffectiveMachineCode` bounds the canonizer's computability, not its
cost, so `TMSAT_mem_NP`/`TMSAT_NPComplete` were false at their stated
generality (Argument A's lawful tagged scheme deciding a diagonal language
`A ∉ EXP` on trivial instances) — while the definition, the other ten
statements, and `TMSAT_NPHard` survived. All round-1 findings are repaired in
this commit, including **the chapter's first statement-level repairs** (two
signatures gain a hypothesis). The gate closes on zero blockers/majors.
Record findings in `audits/ch2-phase3-reaudit-findings.md`.

## Resolution of the round-1 findings (verify each)

| Round-1 finding | Resolution in `8b09a184` |
|---|---|
| 1 blocker — `TMSAT_mem_NP` false at every `EffectiveMachineCode` | The signature now reads `TMSAT_mem_NP (c : EffectiveMachineCode) (hc : PolyBound c.canonizerTime)` — the finding's first proposed fix (minimal hypothesis; no new code interface; the frozen Chapter-1 contracts untouched; `Complexity.PolyBound` is the audited phase-1 numerical helper). The docstring states the counterexample scheme and why the hypothesis is load-bearing; the sketch carries the finding's quantified budget chain (`C_α ≤ 3r + 14·H + 50` via `h, q, N ≤ L ≤ H` and `Turing.MultiTapeTM.output_length_le`) and the finding's own caveat as a **named fill obligation**: the public `timed_universal` exposes its constant only existentially, so the fill needs a new public quantitative bridge in the `Universal` module, requested through the standing shared-file mechanism and flagged at its own audit — the sketch says explicitly that a prose obligation alone cannot discharge the budget |
| 2 blocker — `TMSAT_NPComplete` inherits the falsity | Same hypothesis added to its signature; docstring records that without it the Argument-A scheme's `TMSAT` is `NP`-hard yet outside `NP`. `TMSAT_NPHard` **stays at plain `MachineCode`**, per the finding |
| 3 major — hardness sketch's unary emissions (exact `Q` not time-constructible; majorization changes the language; `T'` left as description) | The sketch adopts the finding's exact-value discipline verbatim: the three-case emission table (`C₀ = 0` — empty run; `C₀ > 0, c₀ = 0` — fixed constant from finite control; `C₀ > 0, c₀ > 0` — `timeConstructible_poly C₀ (c₀ - 1)`), the false-positive counterexample recorded (`C₀ = c₀ = 0`, `L = V = {[true]}`), majorization applied **only to the deadline**, and the finding's explicit formula `T' n = D·(n+1)^(2er)` with its parameters and the `s + 1 ≤ (C₀+3)(n+1)^r` inequality transcribed, computed by `timeConstructible_poly D (2er - 1)` |
| 4 minor — parity flip in the membership split rejection | The sketch now rejects **even** lengths and splits an odd `N` at `(N-1)/2`, citing the finding |
| 5 minor — fallback-independence prose overbroad | `SAT.lean`'s deviations bullet now states that each language's malformed-input branch follows its own predicate on the fallback (the width-four counterexample recorded) and that the reduction maps malformed inputs to the serialization of the **transformed** fallback |
| 6-8 notes | No statement changes, per the findings; the syntax-validation-before-evaluation order, the toolchain pin, the campaign-formula restriction on the unary-size claim, and the phase-4 DNF-fragment guidance are all retained/recorded |

## Repository-side attestations (maintainer, local machine — verify or challenge)

1. **Scope.** `8b09a184` touches exactly: `ClassNP/TMSAT.lean`,
   `ClassNP/SAT.lean`, the plan (two decision rows), and adds the round-1
   findings file verbatim. **Statement drift, enumerated**: exactly 2 theorem
   signatures changed (the hypothesis additions), 0 definitions changed, one
   precise import added (`ClassNP.PolyTime`, for `PolyBound`); `SAT.lean` is
   comment-stripped identical to `1a7554d1`. Everything else — all five
   phase-3 files' definitions, the other ten statements, all earlier phases —
   byte-identical.
2. **Elaboration.** The repaired modules and the `ClassNP` facade re-gated at
   `8b09a184`, and a full 48-module fresh sweep run at this commit: zero
   `error:` lines, zero gate failures, exactly **45** admissions, distribution
   unchanged (12 phase-3: 2/3/3/4).
3. **Erratum, disclosed** (and its correction): the comment-only checks
   attested for the phase-2 closing sweep and initially run for this round's
   `SAT.lean` had invoked the comment-stripping script with a filename,
   though it reads stdin — producing empty output on both sides, a vacuous
   comparison. Re-run correctly at repair time: the phase-2 closure files are
   comment-stripped **identical** across `e1e68ebd..487f58cb` (the original
   claim was true; its verification was not), and this round's `SAT.lean`
   comment-only / `TMSAT.lean` two-signature drift is established by the
   corrected recipe. Challenge or reproduce from the attached sources.
4. **Policy.** Style lint: zero campaign FAIL; six Chapter-1 WARNs unchanged.
   Admission sketches intact; the two repaired statements keep statement
   prose + sketch.

## Brief for the auditor

A narrow round: two signatures, three sketch/prose texts, and the plan rows.

1. Verify the resolution table row by row against the source.
2. **Is the hypothesis the right minimal strengthening?** `PolyBound
   c.canonizerTime` per your Argument A: sufficient via your budget chain;
   check the transcription of that chain into the sketch is faithful, and
   that no *other* phase-3 statement quietly needs the same hypothesis
   (`TMSAT_NPHard` deliberately does not — re-confirm).
3. **Re-check the repaired hardness sketch** as a faithful rendering of your
   Argument B: exact-value cases, deadline majorization only, the `T'`
   formula and its inequality, the `timeConstructible_poly` instantiations
   (`c₀ - 1`, `2er - 1` — off-by-one check welcome).
4. Re-read the corrected parity text and the fallback prose.
5. Assess attestations 1-4, including the disclosed erratum and whether its
   correction restores the evidentiary basis of the phase-2 closure claim.

## Scope

| Item | Where |
|---|---|
| Files under audit | `ClassNP/TMSAT.lean` (2 changed signatures + changed docstrings/sketches), `ClassNP/SAT.lean` (changed prose only), `AroraBarakChapter2Plan.md` (the two new rows) |
| Context | `audits/ch2-phase3-findings.md` (round 1 — your report), `audits/ch2-phase3-pack.md`, the phase-1/2 audit records, both plans, `workflow.md`, `policy.md`, `scripts/ab_ch1_module_order.txt`; all 48 modules + root attached |
| Out of scope | everything certified in round 1 (the 16 definitions, the other ten statements, the serialization layer); closed earlier gates; the human-reserved design question; phase-4 material |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.
