# External audit pack — Phase 1 (core model, classes, oracle wrapper)

Instantiated from `audits/TEMPLATE.md`. Hand this file and the attachments to an external
LLM from a different vendor, fresh context. Record findings in
`audits/phase1-findings.md`. Findings must be addressed before phase 2 begins.

**Status note:** at pack-creation time the phase-1 files are a sorry-skeleton and have
not yet been elaborated by Lean in this checkout (dependencies not fetched); the audit
targets *statements*, which is unaffected, but the auditor should know that elaboration
errors may still force cosmetic changes.

---

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 formalization: definitions, theorem
statements, and remaining `sorry`s. The proofs that exist are machine-checked or pending —
do not review tactic scripts. The failure modes you are hunting are:

1. **Infidelity** — a definition that does not mean what Arora-Barak Chapter 1 means.
2. **Trivialization** — a definition or statement satisfiable for degenerate reasons.
3. **Unprovability** — a `sorry`d statement false as literally stated (boundary cases:
   empty input, `n = 0`, `k = 0` tapes, constant absorption, halting-in-0-steps).
4. **Missing hypotheses** — especially finiteness, positivity, well-formedness.

For **every definition** in scope: restate it in your own mathematical English *without
reading the docstring first*, then compare against the cited source location and report
any daylight. For **every `sorry`d theorem**: argue in 2-5 sentences why it is true as
literally stated, or exhibit the problem. Attempt at least **5 adversarial
instantiations**; suggested starting points are in "Specific questions" below. Propose
missing machine-checkable sanity theorems.

Do not give a blanket approval. Your deliverable is the findings table; an empty table
must be accompanied by per-definition restatements justifying it.

## Scope

| Item | Where |
|---|---|
| Lean files under audit | `TCSlib/Complexity/TuringMachine/{Configuration,Deterministic,Finite,Oracle}.lean`, `TCSlib/Complexity/ClassP/{DTIME,TimeConstructible,P,Examples}.lean` |
| Source text | Arora & Barak, *Computational Complexity: A Modern Approach*, CUP 2009 — Chapter 1 (pp. 9-37), esp. §1.2, §1.3, Definitions 1.3/1.12/1.13, Examples 1.1/1.4; §3.4 (Definition 3.6, oracle machines) |
| Plan/context documents | `AroraBarakChapter1Plan.md` (architecture §3), `policy.md` §2-3 |
| Out of scope | tactic proofs; the upstream design of the two vendored cslib files *except* where our layer depends on a property of theirs (flag such dependencies if they look wrong) |

## Known deviations (declared — verify they are benign, flag any others)

* Tape alphabet is `Option Symbol` with blank = `none`; for classes, `Symbol := Bool`
  (three tape symbols) instead of AB's `{▷, □, 0, 1}`; bidirectional tapes, no start
  symbol (AB Claim 1.8 direction).
* Single halting state (`state = none`); accept/reject read off the output tape, not
  from accepting states.
* Input head may move freely but is clamped to one cell beyond the input on each side.
* `DTIME`'s constant ranges over all `c : ℕ` (the `c = 0` bound is unsatisfiable, so
  this matches AB's `c > 0`).
* `P = ⋃ c, DTIME (n^c + 1)` — the `+ 1` repairs the empty-input degeneracy.
* `PAL ∈ DTIME (n + 1)` rather than AB's "`3n` steps" (constant absorbed, empty input).
* `TimeConstructible` uses `Nat.bits` (little-endian) for `⌞·⌟` and demands the exact
  `T n` bound with no constant slack, faithfully to AB — flagged by the authors as
  possibly too strict (see question 5).
* Oracle machines: query = query-tape contents from cell 0 rightward to the first blank
  (`[]` if the nonnegative half-tape has no blank); the answer step changes only the
  state; `qYes`/`qNo` are ordinary states.
* Bundled `FinTM` carries `Fintype`/`DecidableEq` as data; the alphabet parameter is not
  bundled (classes fix it to `Bool`).

## Specific questions for this phase

1. `MultiTapeTM.ComputesInTimeAndSpace` requires `state = none` *at* step `t`. Since
   halting is absorbing, "halts within `t` steps" and "state is `none` at step `t`"
   should coincide — confirm there is no off-by-one or "exactly at `t`" reading anywhere
   downstream (`FinTM.ComputesInTime`, `DecidesInTime`, `DTIME`).
2. `FinTM.DecidesInTime` uses the classical `indicator` and demands output exactly
   `[b]`. Is anything lost versus AB's "outputs 0/1"? Consider a machine that emits
   extra output symbols before halting.
3. Can any degenerate machine place an undesired language in `DTIME T` for small `T`
   (e.g. `T = 0`, `T = 1`)? Conversely, is the intended content of `DTIME` reachable —
   does the definition quantify the way AB Definition 1.12 does?
4. `P`'s `+ 1` deviation: confirm `⋃ c, DTIME (n^c + 1)` equals the standard class, and
   that nothing (e.g. `DTIME (fun n => 1)` content) is unintentionally included or
   excluded.
5. `TimeConstructible`: is `id` time constructible under the exact-bound reading in our
   model (write-only, left-to-right output tape)? If provably not, say so — the authors
   will switch to the constant-slack variant.
6. Oracle `queryString`: does "cells 0 upward to first blank" together with "`[]` when no
   blank exists" create any exploitable mismatch (e.g. a machine whose query depends on
   junk left beyond the first blank, or the empty-query convention colliding with
   `[] ∈ O`)? Is the one-step answer semantics faithful to AB Definition 3.6?
7. `OracleTM.ofMultiTapeTM` and the two sorry'd lockstep theorems: check the statements
   are literally true; pay attention to `Cfg.embedOracle` (blank query tape, head at 0)
   versus `initCfg` (all tapes blank) and to whether `Sum.inr` states are truly
   unreachable.
8. Adversarial instantiations to attempt: a 0-work-tape machine (`k = 0`); the machine
   whose transition always halts immediately (what does it decide, and in what time?);
   the empty input everywhere; an oracle machine with `qQuery = q₀`; a `FinTM` whose
   `State` is `Fin 1`.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.
