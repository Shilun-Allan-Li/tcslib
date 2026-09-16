# Phase 1 — audit loop resolutions (CLOSED)

Protocol: `AroraBarakChapter1Plan.md` §5 "Audit protocol"; packs and findings in this
directory. External auditor: cross-vendor LLM per decision log (option (a)).

## Round 1 (`phase1-pack.md` → `phase1-findings.md`, audited at `65a3fe52`)

3 majors, 5 minors, 3 notes; all 8 original sorries confirmed true as stated.
All findings accepted; resolved in commit `3a45aa2f`:

| Finding | Resolution |
|---|---|
| 1 major — strict `TimeConstructible` refutes AB's `id` example | Definition repaired to `∃ c > 0, … c·(T n + 1)`; refutation documented; `timeConstructible_id` obligation added |
| 2 major — oracle special states may coincide | `OracleTM.WellFormed` added; `ofMultiTapeTM_wellFormed` proved |
| 3 major — false constant-overhead query-tape claim | Corrected to polynomial overhead with the parity counterexample cited |
| 4 minor — undeclared output/init deviations | Declared in `DTIME.lean`; simulations recorded as phase-2 obligations (partial waiver: proofs deferred by design) |
| 5 minor — citation is Definition 3.4, not 3.6 | Fixed in code and plan |
| 6 minor — `ofMultiTapeTM` docstring vs `qQuery` | Reworded |
| 7 minor — P.lean prose mismatches | Fixed |
| 8 minor — plan overstates `FinTM`/oracle sanity | Plan corrected; converse `plainEmptyOracle` elimination added |
| 9-11 notes — sanity menu | Curated subset added; full menu retained in findings for the fill phase |

## Round 2 (`phase1-reaudit-pack.md` → `phase1-reaudit-findings.md`, audited at `3a45aa2f`)

**Zero blockers, zero majors.** All round-1 resolutions verified; all 8 new sorries
confirmed true (16 total); the auditor supplied a complete 4-state witness machine and
step-count analysis for `timeConstructible_id`, the full field calculation for
`runFrom_plainEmptyOracle`, the two-invariant induction for the query-tape bounds, and
the `mem_P_iff` constant arithmetic — all reusable in the fill phase. 5 prose minors and
2 notes; resolved in the closing commit:

| Finding | Resolution |
|---|---|
| 1 minor — TimeConstructible prose (old budget in intro; overstated example restoration; timed-UTM attribution) | Intro states the repaired budget; examples qualified by small-input normalization; supplied-budget vs generated-bound uses distinguished |
| 2 minor — "requires patching the machine" | Corrected: same machine, exceptional bounds absorbed into the constant |
| 3 minor — unpadded-union emptiness needs positive-degree qualification (`0^0 = 1`) | Qualified; degree-0 component identified as `DTIME 1` |
| 4 minor — plan/`FinTM` docstring still attribute write-only output to AB §1.2; stale `DTIME(3n)` target | Plan §§1-2 and layout corrected; `FinTM` docstring qualified with the declared variations |
| 5 minor — aliasing-loop descriptions under-qualified | "After a positive answer" / "once the common query state is reached" qualifications added; `qYes = qNo` obliviousness noted |
| 6 note — length bound alone doesn't certify fallback unreachability | `runFrom_workTapes_blank` certificate lemma added (sorry'd, audited sketch) |
| 7 note — statements survive adversarial cases | No change; proofs to be completed without weakening statements |

## Gate status

**CLOSED.** Phase 2 is unblocked. Carried obligations, tracked in the plan:

- Fill phase: 17 sorries, each with a sketch; round-1/round-2 findings contain worked
  constructions to reuse (PAL machine, counter machine, lockstep field calculations).
- Phase 2 (robustness) additionally owes: append-only vs read-write output simulation
  (constant overhead), start-marker/initialization conventions, persistent vs
  auto-erased query tape (polynomial overhead only — constant provably impossible).
- Chapter 3 (oracle classes): finite, `WellFormed` oracle-machine bundle before any
  oracle class is defined.
