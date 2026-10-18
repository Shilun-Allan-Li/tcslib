# External audit pack — Chapter 2, Phase 4 (Cook-Levin)

Audits commit `6484ce88` on `complexity/arora-barak-ch1`. This is the
**fourth and final statement phase of the Chapter 2 campaign**
(`AroraBarakChapter2Plan.md` §4) — the summit — opened after the phase-3 gate
closed in two rounds (`audits/ch2-phase3-resolutions.md`). The phase lands
the snapshot/locality layer over oblivious machines, the Cook-Levin hardness
statements, the DNF dual layer, and `TAUTOLOGY` — **14 definitions and 14
sorried statements, zero proofs** — across four new math modules and one
facade. The product under audit is the statements, their conventions, and
their proof sketches; the `SAT_NPHard` sketch is the largest of the campaign
and is this round's center of gravity. The gate closes on zero
blockers/majors. Record findings in `audits/ch2-phase4-findings.md`.

Source text: [AB09] §2.3.2-2.3.4 (Lemma 2.11: snapshots, obliviousness,
conditions 1-4, eq. (2.3), footnotes 5-6, Figures 2.2-2.3, pp. 45-49),
Theorem 2.10 (p. 45), Example 2.12 (p. 46), Claim 2.13 (p. 46), §2.6.1
(Definitions 2.19-2.20, Example 2.21, pp. 55-56).

## Repository-side attestations (maintainer, local machine — verify or challenge)

Source facts vs. execution claims separated per standing practice.

1. **Freeze.** Commit `6484ce88` touches exactly: five new Lean files
   (`Formulas/DNF.lean`, `CookLevin/Snapshot.lean`, `CookLevin/Hardness.lean`,
   `CookLevin.lean` facade, `ClassNP/Tautology.lean`), import/Contents
   additions in the `Formulas` and `ClassNP` facades and the root
   `TCSlib.lean`, five inserted lines in `scripts/ab_ch1_module_order.txt`
   (now 53 modules — attached), and the plan (the Astra prior-art survey row
   and the seeded-questions row). Zero previously audited proof-bearing
   modules changed; all phase-1/2/3 statements byte-identical with their
   closed gates.
2. **Elaboration.** Full 53-module fresh-olean sweep, Lean 4.25.0 / mathlib
   `029db123ddaa`: zero `error:` lines, zero gate failures, exactly **59**
   admissions — 19 + 14 + 12 from the closed phases, unchanged, plus exactly
   **14 new** (2 `DNF` / 5 `Snapshot` / 5 `Hardness` / 2 `Tautology`).
3. **Admissions and axiom prints.** Tree-wide `sorry` count exactly 59,
   every admission under a **Proof sketch**. On the fresh tree: the eight
   Chapter-1 headline prints remain `[propext, Classical.choice,
   Quot.sound]`; the new definitions print axiom-free or classical-only; the
   new sorried statements show `sorryAx` as expected.
4. **Policy.** Style lint: zero campaign FAIL (legacy `NPReductions/*`
   untouched, outside the surface); six Chapter-1 size WARNs unchanged. New
   files 105/252/202/23/131 lines.
5. **New surface inventory.** 14 definitions — 3 DNF-layer (`evalDNF`,
   `dual`, `DNFTautology`, in the `Std.Sat.CNF` namespace like the phase-3
   layer), 8 snapshot-layer (`Snapshot`, `snapshotAt`, `inputPosAt`,
   `workPosAt`, `prevVisit`, `stepState`, `writtenOrKept`, `emitted`,
   `inputBitAt` — nine names, `Snapshot` is an abbrev), 3 language-layer
   (`coNPHard`, `coNPComplete`, `TAUTOLOGY`) — and 14 sorried theorem
   signatures; zero proofs; no new external imports (the DNF layer reuses
   the phase-3 carrier); the `prevVisit` definition is computable
   (`List.range`/`filter`/`max?` with `BEq ℤ`), no choice.

## What is under audit

| Module | Definitions | Sorried statements |
|---|---|---|
| `Formulas/DNF.lean` | `evalDNF` (OR of ANDs on the shared carrier), `dual` (literal-negating, size-preserving), `DNFTautology` | `evalDNF_dual` (pointwise De Morgan), `dnfTautology_dual_iff` |
| `CookLevin/Snapshot.lean` | `Snapshot`, `snapshotAt`, the reference-input schedule `inputPosAt`/`workPosAt`, `prevVisit` (`none` on first visits), the reconstruction functions `stepState`/`writtenOrKept`/`emitted`, `inputBitAt` | `oblivious_schedule_eq`, `snapshotAt_zero`, `snapshotAt_state_succ`, `snapshotAt_inputSymbol`, `snapshotAt_workSymbol` (**"computation is local"** — [AB09] eq. (2.3) with footnote 6, multi-tape) |
| `CookLevin/Hardness.lean` | — | `NPHard.polyTimeReducible` (**flagged**: new statement on audited phase-1 notions), `SAT_NPHard` ([AB09, Lemma 2.11] — the summit sketch: normalization through `oblivious_of_mem_DTIME`, variables, six clause families, both correctness directions, the emitting machine), `SAT_NPComplete`, `SAT3_NPHard`, `SAT3_NPComplete` |
| `ClassNP/Tautology.lean` | `coNPHard`, `coNPComplete` (**flagged**: new definitions on audited notions), `TAUTOLOGY` (DNF fragment, shared serialization, fallback flips sides) | `TAUTOLOGY_mem_coNP`, `TAUTOLOGY_coNPComplete` ([AB09, Example 2.21]) |

## Brief for the auditor

Ground rules as always: closed gates (Chapter 1, phases 1-3) are trusted
context; textbook item numbers are the pack's citations; human-reserved
questions' dispositions out of scope. Priorities:

1. **Adversarially re-derive the locality theorems** — the mathematical heart.
   `snapshotAt_workSymbol` especially: is "the cell's content is the last
   visit's written-or-kept symbol, blank on first visits" correct against
   the model's *optional* write (`writtenOrKept`'s `getD` branch), the halted
   branches, boundary times (`t = 0`), and `prevVisit`'s `max?`-over-filter
   definition (membership and maximality; the reference-input positions vs.
   the run on `x`)? Does `oblivious_schedule_eq` really follow from the
   positions-only `Turing.FinTM.Oblivious`?
2. **Design question (a) — acceptance as "no step emits `false`".** The
   tableau replaces [AB09]'s condition 4 by forbidding `false`-emissions,
   with "at least one emission" supplied by the decider contract
   (`DecidesInTime` totality within the horizon) in the correctness
   argument, not by clauses. Stress this: is the argument airtight for
   *both* directions of satisfiability, including runs that halt early,
   emit nothing, or would emit after the horizon (impossible — why exactly)?
3. **The `SAT_NPHard` sketch end to end**: the normalization chain
   (`mem_P_iff` → `timeConstructible_poly` at the enlarged `A, d ≥ 1` →
   `oblivious_of_mem_DTIME`; is the exact-value discipline respected —
   nothing about the *certificate length* is majorized?); the variable
   packing arithmetic; each clause family's constant-size claim and its
   Claim-2.13 + relabel derivation; the junk-block totalization and the
   bitwise-pinning uniqueness argument; the induction in direction (⇒); the
   emitting machine's obligations (clocked schedule simulation on the
   *definitional* reference input, `prevVisit` by trajectory comparison,
   unary index emission) and its budget.
4. **Design questions (b)/(c)/(d)**: first-visit-blank vs. [AB09]'s
   `prev(i) = 1`; the budget horizon under positions-only obliviousness
   (halted branches in every reconstruction function); the certificate as
   free `y`-variables with `x` pinned by unit clauses.
5. **The DNF layer and `TAUTOLOGY`** (questions (e)/(f)): the dual's
   conventions (empty formula/clause flipping), the De Morgan statements,
   the fragment rendering's honesty (round-1 finding-7 guidance), the
   fallback flipping sides, `TAUTOLOGY_mem_coNP`'s reuse of the `(1,1)`
   certificate machinery with the dual evaluator (the mirrored
   evaluation-congruence obligation is *named*, not stated — assess whether
   it should be stated), and Example 2.21's reduction through
   `decode`-`dual`-`serialize` on every string.
6. **`NPHard.polyTimeReducible`** and the completeness assemblies; the
   `coNPHard`/`coNPComplete` definitions against Definitions 2.19-2.20's
   context.
7. The plan's Astra prior-art survey row: assess the recorded reasons as
   stated (the artifact itself is not attached and is not audit material;
   the row's claims about *our* campaign's compatibility are what is under
   review).

## Scope

| Item | Where |
|---|---|
| Files under audit | `Formulas/DNF.lean`, `CookLevin/Snapshot.lean`, `CookLevin/Hardness.lean`, `CookLevin.lean`, `ClassNP/Tautology.lean` (all new), the facade/root diffs, the order-list insertion, the two plan rows |
| Context | the phase-1/2/3 audit records (`audits/ch2-phase{1,2,3}-*`), both plans, `workflow.md`, `policy.md`, `scripts/ab_ch1_module_order.txt`; all 53 modules + root attached |
| Out of scope | everything certified at closed gates; the human-reserved design question; the fill campaign's machine constructions beyond sketch-level obligation naming; general Boolean formulas (deliberately unformalized) |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.
