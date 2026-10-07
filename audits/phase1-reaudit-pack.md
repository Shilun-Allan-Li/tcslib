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
