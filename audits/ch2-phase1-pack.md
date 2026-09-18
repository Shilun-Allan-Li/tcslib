# External audit pack — Chapter 2, Phase 1 (classes and reductions)

Audits commit `ab82bb6a` on `complexity/arora-barak-ch1`. This is the **first
statement phase of the Chapter 2 campaign** (`AroraBarakChapter2Plan.md`),
opened after the Chapter 1 campaign closed fully audited (21/21 proved,
admission-free, blueprint-extracted; see `AroraBarakChapter1Plan.md` §7 and
`audits/epoch4-resolutions.md`). The phase lands the chapter's class
definitions and reduction notions with **19 sorried statements** under a new
`TCSlib/Complexity/ClassNP/` tree — no proofs are audited this round; the
product under audit is the *statements*, their *conventions*, and their
*proof sketches*, before any fill work begins (the Chapter-1 protocol).
Record findings in `audits/ch2-phase1-findings.md`.

Source text: [AB09] ch. 2 — Definition 2.1 (p. 39), Claim 2.4 (p. 41),
Definition 2.7 and Theorem 2.8 (pp. 42-43), §2.6.1-2.6.2 (Definitions
2.19-2.20, pp. 55-56), and Exercises 2.1, 2.8, 2.9, 2.23, 2.24, 2.25, 2.27.

## Repository-side attestations (maintainer, local machine — verify or challenge)

1. **Chapter-1 freeze.** The two Chapter-2 commits (`3e35ba23` plan,
   `ab82bb6a` skeleton) add only new files plus six appended lines in
   `scripts/ab_ch1_module_order.txt` (now 40 modules); **zero Chapter-1 Lean
   files are touched** (verified by path enumeration over the span
   `f7b8ad0a..ab82bb6a`). The audited Chapter-1 surface is exactly as closed
   at epoch 4.
2. **Elaboration.** Full 40-module fresh-olean sweep via the strengthened
   `scripts/lean_check_tree.sh`, Lean 4.25.0 / mathlib `029db123ddaa`: zero
   `error:` lines, zero gate failures, and exactly **19** `declaration uses
   'sorry'` warnings — all in `ClassNP/` (3 PolyTime / 2 NP / 4 CoNP / 3 EXP /
   7 Reductions), none anywhere in the Chapter-1 tree.
3. **Admissions inventory.** Tree-wide `sorry` count is exactly 19; every one
   sits under a docstring whose **Proof sketch** names only stated results of
   this development (`scripts/style_lint.py`'s sketch check passes). The eight
   Chapter-1 headline axiom prints remain admission-free (re-printed on the
   fresh olean tree); each sorried Chapter-2 statement depends on `sorryAx`,
   as expected at a statement phase.
4. **Policy conformance.** `scripts/style_lint.py` over the campaign tree:
   zero FAIL; the six WARNs are the recorded Chapter-1 size escalations,
   unchanged. All 29 new public declarations carry statement-prose docstrings;
   the new facade imports all five children; all six new files are under 150
   lines.
5. **New surface inventory** (programmatic): 10 definitions + 19 sorried
   theorems + 1 scoped notation, all in namespace `Complexity`; no new
   imports beyond in-repo modules (`Composition`, `ClassP.P`,
   `Uncomputability.Halting`); no axioms, no `set_option` additions beyond the
   standard header, no instances.

## What is under audit

| Module | Definitions | Sorried statements |
|---|---|---|
| `ClassNP/PolyTime.lean` | `PolyBound` (`∃ C c, p n ≤ C·(n+1)^c`), `PolyTimeComputable` (FP via `ComputesFunInTime` at `C·(n+1)^c`) | `polyTimeComputable_id`, `PolyTimeComputable.output_length_le`, `PolyTimeComputable.comp` |
| `ClassNP/NP.lean` | `NP` — [AB09, Definition 2.1] with the verifier as a **language** `V ∈ P` and certificates of **exact** length `p |x|` concatenated as `x ++ u` | `P_subset_NP`, `mem_NP_iff_exists_length_le` (Exercise 2.1) |
| `ClassNP/CoNP.lean` | `coNP := {L | Lᶜ ∈ NP}` (Definition 2.19) | `compl_mem_P` (**new statement on the audited Chapter-1 class — flagged**), `mem_coNP_iff_forall` (Definition 2.20 / Exercise 2.24), `P_subset_NP_inter_coNP`, `NP_eq_coNP_of_P_eq_NP` |
| `ClassNP/EXP.lean` | `EXP := ⋃ c, DTIME (2^(n^c))`, `ExpBound`, `NEXP` (Exercise-2.27 certificate form) | `P_subset_EXP`, `NP_subset_EXP`, `EXP_subset_NEXP` |
| `ClassNP/Reductions.lean` | `PolyTimeReducible` (scoped `≤ₚ`), `NPHard`, `NPComplete` | `PolyTimeReducible.refl`/`.trans`, `mem_P_of_polyTimeReducible`, `P_eq_NP_of_NPHard_mem_P`, `NPComplete.mem_P_iff`, `HALT_NPHard`, `HALT_not_mem_NP` (Exercise 2.8, both halves) |

## Brief for the auditor

Ground rules as in every Chapter-1 round (trusted surface; no blanket
approval; there are no proofs to audit — sketches are audited for
*implementability against the stated Chapter-1 API*, and statements for
*fidelity and freedom from pathology*). Priorities:

1. **Blind-restate all 10 definitions and 19 statements** against the cited
   [AB09] items and flag any formula divergence. The Chapter-1 API they build
   on: `Complexity.DTIME`/`P`/`mem_P_iff` (deciders output `[true]`/`[false]`
   via the indicator), `Turing.FinTM.ComputesFunInTime`, the guarded
   composition combinators, `Turing.pairEncode` (code-first),
   `Complexity.HALT` (totalized `false` off the pair image), and
   `Turing.EffectiveMachineCode`.
2. **The `V ∈ P` verifier rendering** (plan §2, design question a): [AB09]
   quantifies over a machine `M` with `M(x, u) = 1`; we quantify over a
   language `V ∈ P`. Argue equivalence with the machine form — or exhibit a
   pathology (the Chapter-1 phase-3 round found a genuine one in the analogous
   spot, Argument A; this is the deliberate stress test). Pay attention to:
   the definition never splits `x ++ u`; different `(x, u)` pairs can
   concatenate to the same string; `V` is constrained by the equivalence only
   on strings of the form `x ++ u` with `|u| = p |x|`.
3. **Exact-length certificates + Exercise 2.1** (design question b): verify
   the equivalence claim and independently re-derive the (⇐) padding
   construction. The maintainer's sketch records one known trap — a
   marker-free all-`false` certificate region would let naive stripping eat
   into `x`; the sketch's fix recovers the split from the strictly monotone
   padded length before stripping. Confirm the fix, or find what it still
   misses (non-monotone `p` in the source form; `p |x| = 0`; empty `x`).
4. **`PolyBound`'s normal form** `C·(n+1)^c` vs Chapter 1's `n^c + 1` (design
   question c): confirm the two bound the same classes and that the
   `(n+1)^c` form's monotonicity is used soundly where sketches invoke
   majorants.
5. **`compl_mem_P`** (design question d): a new statement about the audited
   Chapter-1 class, placed in Chapter-2's tree. Check the statement (nothing
   in `DecidesInTime` obstructs complementation), and the sketch's use of
   `computesFunInTime_ifEq`/`exists_comp_partial`.
6. **`EXP`/`NEXP` conventions**: `⋃ c : ℕ` includes `c = 0, 1` where [AB09]
   writes `c > 1` — confirm the union is unchanged. `NEXP`'s certificate form
   vs the (deferred) `NTIME` form: is the Exercise-2.27 rendering the standard
   one, and is `EXP_subset_NEXP`'s split-recovery sketch sound (`n + p n`
   strict monotonicity; binary-power evaluation cost)?
7. **Exercise 2.8's two sketches**: the searcher machine (loop-forever branch
   on exhausted candidates — confirm a deliberately divergent state exists in
   our model), the `universal_quadratic`-pattern coding of the searcher, the
   constant-prefix `pairEncode α ·` reduction's linear-time machine, and the
   `HALT_not_mem_NP` chain through `NP ⊆ EXP` and `HALT_not_computable`.
8. Assess attestations 1-5 and the `≤ₚ` notation scoping (design question e).

## Specific questions

1. In `NP`'s membership equivalence, can a pathological `V ∈ P` — arbitrary
   off the constrained strings — ever change the defined class relative to
   [AB09]'s machine form? Exhibit or refute.
2. `P_subset_NP` takes `p = 0`, `V = L`. Does anything break for `L = ∅`,
   `L = univ`, or `x = []`?
3. Is `Complexity.NP` monotone-`p`-normalizable *inside the exact-length
   form* (i.e. can `p` be replaced by `C(n+1)^c` without Exercise 2.1's
   detour), or is the bounded-length detour genuinely needed?
4. `NP_subset_EXP`'s enumerator: the sketch's counter has width `p n`
   computed from the majorant — but membership uses the *original* `p`.
   Confirm the enumerator enumerates certificates of length exactly `p n`
   (not the majorant), or identify the repair (e.g. enumerate all lengths
   `≤` majorant and re-check the length equality — cost still exponential-
   bounded).
5. `EXP := ⋃ c, DTIME (2^(n^c))`: at `n = 0` every bound is `2^0 = 1` or
   `2^1 = 2` — do the Chapter-1 `DTIME` emptiness conventions
   (`DTIME_eq_empty_of_exists_zero`) interact with any statement here?
6. `HALT_NPHard` is stated per effective scheme `c`. Should it be (is it
   provable) for *every* `Turing.MachineCode`, or does the searcher's coding
   genuinely need effectivity? (Compare Chapter 1's Theorem 1.10 vs 1.11
   split.)
7. The scoped notation `≤ₚ` — any collision risk with Mathlib or in-repo
   notation at these precedences?

## Scope

| Item | Where |
|---|---|
| Files under audit | the six `ClassNP/` files (statements + sketches only) |
| Source text | [AB09] ch. 2, pp. 38-44 and 55-57 + the cited exercises |
| Context | `AroraBarakChapter2Plan.md` (esp. §2 and the decision log's seeded questions), `AroraBarakChapter1Plan.md` (methodology + Chapter-1 conventions), `policy.md`; the Chapter-1 API modules attached in the bundle |
| Out of scope | all Chapter-1 mathematics (closed rounds); proof tactics (none exist yet); the phase-2/3 design questions (previewed in the plan, audited in their own rounds) |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.
