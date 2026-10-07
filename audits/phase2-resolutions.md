# Phase 2 — audit loop resolutions (CLOSED)

Protocol: `AroraBarakChapter1Plan.md` §5 "Audit protocol". External auditor:
cross-vendor LLM per decision log.

## Round 1 (`phase2-pack.md` → `phase2-findings.md`, audited at `2917a1b9`)

4 majors, 6 minors, 3 notes — **no theorem formula refuted**; all 11 new sorries
assessed true as stated, with reusable constructions supplied (masked-witness clock,
`B(n)` fixed-sweep oblivious simulation, visited-zone sums, constant-absorption
calculations, the stationary-head counterexample). All findings accepted; resolved in
commit `85b66f2a`, entirely at the prose/sketch/plan level:

| Finding | Resolution |
|---|---|
| 1 major — "frozen heads force length-determined halting" is false | Implication removed everywhere; `TimeConstructible` correctly attributed to the construction; Cook-Levin normal-form conjuncts flagged for Ch. 2 |
| 2 major — inadequate oblivious-simulation sketch | Replaced by the audit's corrected five-step construction |
| 3 major — convention obligations wrongly "discharged" | Re-recorded as **waived** with restricted claims; `Composition.lean` rewritten |
| 4 major — ModelInvariance overstated | Stated at delivered strength (alphabet: `DTIME` up to constants; tape count: `P` only) |
| 5-10 minors | In-model-analogue framing + palindrome separation (1.6); output-schedule and Exercise-1.5-scope clarifications; all-blank block code (1.5); tagged payloads and `k = 0` (1.6); piecewise fold coordinate with origin tags and safe-halt (1.8) |
| 11-13 notes | Documented; stale scope paragraph aligned |

## Round 2 (`phase2-reaudit-pack.md` → `phase2-reaudit-findings.md`, audited at `85b66f2a`)

**Zero blockers, zero majors.** Both corrected load-bearing sketches certified as
adequate proof outlines (the auditor supplied the masked-witness run-relation
induction, the full folding movement table with the concrete alphabet, unary-length
bookkeeping for the copy phase, and the quadratic cost accounting — all reusable at
fill time). 4 minors and 7 notes; minors resolved in the closing commit:

| Finding | Resolution |
|---|---|
| 1 minor — `Γ × Γ` folding alphabet cannot represent mixed blank/symbol cells | Module description and sketch now use `Bool × Option Γ × Option Γ` (origin flag + two independent payloads), `e γ = (false, some γ, none)`, one-transition simultaneous origin initialization |
| 2 minor — residual prose inconsistencies with the waiver | `DTIME.lean` deviations synchronized; `Composition.lean`'s "costs no generality" replaced by the precise in-model statement; the existential-constants restriction narrowed to source-adapted bounds |
| 3 minor — `O(k · L)` vanishes at `k = 0` | Corrected to `O((k + 1) · L)` with the residual work named |
| 4 minor — plan promised a "four-symbol normal form" from phase 2 | Corrected to the one-work-tape *binary* normal form (`FinTM Bool`, three tape symbols); any four-symbol step is a named extra embedding |
| 5-10 notes | No changes required; implementation invariants recorded in the findings for the fill phase |
| 11 note — byte identity not auditor-certifiable | Verified **by us via git**: comment-stripped comparison of all 22 Lean files between `2917a1b9` and `85b66f2a` shows zero non-comment differences. Recorded here as a repository-side verification, not an audit claim |

## Gate status

**CLOSED.** Phase 3 (encodings + universal machine) is unblocked. Carried
obligations, tracked in the plan:

- Fill phase: 28 sorries total, each with an audited sketch; both phase-2 findings
  files contain worked constructions and calculations to reuse.
- Waived (standing): the append-only vs read-write output-tape and initialization
  bridges — revisit only if a downstream result needs a formal bridge; no exact
  [AB09] step count may ever be imported as a formal bound.
- Chapter 2 (Cook-Levin): any use of simultaneous obliviousness, tape restriction, or
  length-determined halting needs its own stated normal-form guarantee.
- Chapter 3 (oracle classes): the persistent-vs-erased query-tape polynomial-overhead
  statement, plus the finite `WellFormed` oracle bundle, before any oracle class.
