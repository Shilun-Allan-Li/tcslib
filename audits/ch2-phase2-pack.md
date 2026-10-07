# External audit pack — Chapter 2, Phase 2 (nondeterminism)

Audits commit `e1e68ebd` on `complexity/arora-barak-ch1`. This is the **second
statement phase of the Chapter 2 campaign** (`AroraBarakChapter2Plan.md` §4),
opened after the phase-1 gate closed on three adversarial rounds
(`audits/ch2-phase1-resolutions.md`: 10 definitions + 19 sorried statements
audited; the round-1 Arguments A/B/D found and repaired, the repairs certified
in rounds 2-3). The phase lands the nondeterministic machine model and its
class layer with **14 new sorried statements** across three new modules; as in
every statement phase, the product under audit is the *statements*, their
*conventions*, and their *proof sketches* — plus, new this phase, **six proved
definitional-unfolding lemmas** whose proofs are part of the audited surface
(attestation 5). The gate closes on zero blockers/majors. Record findings in
`audits/ch2-phase2-findings.md`.

Source text: [AB09] §2.1.2 (the NDTM model and Definition 2.5, pp. 41-42;
Theorem 2.6 with its proof, p. 42), §2.6.2 (`NEXP`, pp. 56-57; Theorem 2.22
with its padding proof, p. 57), Exercises 2.6 (universal NDTM — **deferred**,
out of scope) and 2.27 (`NEXP` without NDTMs — the route our Theorem 2.22
sketch takes).

## Repository-side attestations (maintainer, local machine — verify or challenge)

1. **Freeze.** Commit `e1e68ebd` touches exactly: three new Lean modules
   (`TuringMachine/Nondeterministic.lean`, `ClassNP/NTIME.lean`,
   `ClassNP/Nondeterminism.lean`), import-list + Contents additions in the two
   facades (`TuringMachine.lean`, `ClassNP.lean`), and three inserted lines in
   `scripts/ab_ch1_module_order.txt` (now 43 modules). **Zero previously
   audited proof-bearing modules changed** (path enumeration); the five
   phase-1 `ClassNP/` modules and every Chapter-1 module are byte-identical
   with their closed-gate state.
2. **Elaboration.** Full 43-module fresh-olean sweep via
   `scripts/lean_check_tree.sh`, Lean 4.25.0 / mathlib `029db123ddaa`: zero
   `error:` lines, zero gate failures, exactly **33** `declaration uses
   'sorry'` warnings — the 19 phase-1 admissions unchanged (3/2/4/3/7) plus
   exactly **14 new** (2 `Nondeterministic` / 4 `NTIME` / 8 `Nondeterminism`).
   One module's sketch wording was touched while the sweep was in flight
   (`ClassNP/Nondeterminism.lean`, comment-only); it and the `ClassNP` facade
   were re-gated individually at the committed text (fresh oleans, zero
   errors, same 8 admissions).
3. **Admissions inventory.** Tree-wide `sorry` count is exactly 33; every
   admission sits under a docstring whose **Proof sketch** names only stated
   results of this development. On the fresh tree, the eight Chapter-1
   headline axiom prints remain admission-free
   (`[propext, Classical.choice, Quot.sound]`); the new sorried statements
   depend on `sorryAx` as expected at a statement phase; the six proved
   lemmas print admission-free.
4. **Policy conformance.** `scripts/style_lint.py`: zero FAIL over the
   campaign tree (the pre-campaign legacy `NPReductions/*` files, outside the
   audited surface and untouched by this commit, carry pre-existing FAILs);
   the six Chapter-1 size WARNs unchanged. All new public declarations carry
   statement-prose docstrings; the three new files are 233/160/234 lines,
   under the 600 target.
5. **New surface inventory** (categories separated, per the phase-1 round-2
   convention): **11 definitions** (`NDTM`, `stepWith`, `initCfg`, `runWith`,
   `HaltsWithin`, `FinNDTM`, `MultiTapeTM.toNDTM`, `FinTM.toFinNDTM`,
   `AcceptsWithin`, `FinNDTM.DecidesInTime`, `NTIME`), **14 sorried theorem
   signatures**, and — a deliberate, flagged deviation from the phase-1
   zero-proof convention — **6 proved lemmas**: `runWith_nil`, `runWith_cons`,
   `runWith_append`, `stepWith_of_halt`, `runWith_of_halt`,
   `toNDTM_initCfg`. Justification: the raw NDTM module is the
   nondeterministic counterpart of the vendored `Deterministic.lean`, whose
   `runFrom` algebra is proved where it is defined; each proof is a
   definitional unfolding or a four-line induction, and all six are inside
   the audit surface (brief, item 6). No new imports beyond in-repo modules;
   no axioms; no instances beyond the two bundled-instance attributes
   mirroring `FinTM`; namespaces `Turing`/`Turing.FinNDTM`/`Complexity` as in
   the deterministic layer.

## What is under audit

| Module | Definitions | Sorried statements | Proved |
|---|---|---|---|
| `TuringMachine/Nondeterministic.lean` | `NDTM` (two total transition functions as a `Bool`-indexed field, [AB09] §2.1.2), `stepWith`, `initCfg`, `runWith` (choice word `List Bool`, consumed left to right), `HaltsWithin` (all-branch halting at exact length), `FinNDTM` (bundled finite layer), `MultiTapeTM.toNDTM`, `FinTM.toFinNDTM` | `HaltsWithin.mono`, `MultiTapeTM.toNDTM_runWith` (the embedding collapses every choice word to `runFrom`) | `runWith_nil`, `runWith_cons`, `runWith_append`, `stepWith_of_halt`, `runWith_of_halt`, `toNDTM_initCfg` |
| `ClassNP/NTIME.lean` | `FinNDTM.AcceptsWithin` (some branch halted with output **exactly** `[true]`), `FinNDTM.DecidesInTime` (all-branch halting on every input + acceptance iff membership), `NTIME` ([AB09] Definition 2.5) | `AcceptsWithin.mono`, `NTIME.mono`, `DTIME_subset_NTIME`, `NTIME_eq_empty_of_exists_zero` | — |
| `ClassNP/Nondeterminism.lean` | — | `ntime_poly_subset_NP`, `NP_subset_iUnion_NTIME`, `NP_eq_iUnion_NTIME` (Theorem 2.6); `ntime_expPow_subset_NEXP`, `NEXP_subset_iUnion_NTIME`, `NEXP_eq_iUnion_NTIME` (§2.6.2 reconciled with Exercise 2.27); `EXP_eq_NEXP_of_P_eq_NP`, `P_ne_NP_of_EXP_ne_NEXP` (Theorem 2.22) | — |

## Brief for the auditor

Ground rules as in every round: the closed-gate Chapter-1 and phase-1 surfaces
are trusted context, not re-audit targets; textbook item numbers are the
pack's citations; the human-reserved design questions' dispositions are out of
scope. Priorities, most valuable first:

1. **Design question (a) — acceptance by output.** [AB09] gives NDTMs a
   `q_accept` state; we define acceptance as *halted with output exactly
   `[true]`* (`FinNDTM.AcceptsWithin`), aligning with the deterministic
   `DecidesInTime`, and leave the outputs of non-accepting branches
   **unconstrained**. Is this rendering faithful everywhere it is consumed
   (both Theorem 2.6 directions, `DTIME_subset_NTIME`)? Is the unconstrained
   non-accepting output sound, or must rejecting branches be forced to
   `[false]` for any stated result?
2. **Design question (b) — the totality quantifier.** `DecidesInTime` demands
   `HaltsWithin` on **every** input, members and non-members, per input,
   conjoined with the acceptance equivalence. Assess against Definition 2.5's
   "for every input and every sequence of choices."
3. **Design questions (c)/(d) — choice words.** Finite `List Bool` words
   consumed left to right (vs. `ℕ → Bool` streams), and **exact-length**
   quantifiers in `HaltsWithin`/`AcceptsWithin` with the monotonicity lemmas
   asserting interchangeability with bounded-length forms. Is absorption
   (`runWith_of_halt`) genuinely sufficient everywhere the sketches
   pad or truncate?
4. **Re-derive the Theorem 2.6 compilations adversarially** — this is where a
   ghost of Argument A would reappear. In particular: (i) the
   certificate-shape arithmetic — each direction must land certificates of
   **exact** admissible shape (`2a(n+1)^c ≥ a(n^c+1)` in
   `ntime_poly_subset_NP`; `a·2^((n+1)^c) ≥ a·2^(n^c)` in the exponential
   analogue); (ii) the verifier obligations — unique-split search with the
   explicit no-solution rejection, the input-window **boundary guard** (the
   simulated machine reads `x`, the simulator's input is `x ++ u`), choice
   consumption, output capture, verdict; (iii) the guess-phase branch
   alignment (deterministic phases identical across branches); (iv) the
   truncation arguments; (v) the budget arithmetic landing inside the stated
   unions, including the small-length absorption in the exponential cases.
5. **Question (e) — union padding.** Theorem 2.6 is stated over
   `⋃ c, NTIME (n^c + 1)` (the `Complexity.P` padding, recorded reason); the
   exponential union `⋃ c, NTIME (2^(n^c))` is unpadded and verbatim. Confirm
   both renderings carry the intended content.
6. **The six proved lemmas**: verify the proofs (they are short and are part
   of this round's surface), and that `stepWith`/`runWith` say what the
   docstrings claim — halting absorbing under every choice, one bit per step.
7. **Question (f) — Theorem 2.22 via the certificate form.** The sketch takes
   [AB09, Exercise 2.27]'s route (pad the certificate-form `NEXP` language;
   `mem_NP_iff_exists_length_le` as the interface; no NDTMs), not [AB09]'s
   proof (pad an `NTIME` machine); `NEXP_eq_iUnion_NTIME` reconciles the two
   readings of the statement. Check the padded-language construction —
   pairing, exact-length checks, the malformed-input branches, and the
   exponential-time decider assembly.
8. `DTIME_subset_NTIME` and the embedding: does `toNDTM_runWith` plus the
   indicator contract really give both conjuncts of `DecidesInTime`?

## Scope

| Item | Where |
|---|---|
| Files under audit | `TCSlib/Complexity/TuringMachine/Nondeterministic.lean`, `TCSlib/Complexity/ClassNP/NTIME.lean`, `TCSlib/Complexity/ClassNP/Nondeterminism.lean` (all new), the two facade diffs, the order-list insertion |
| Context | `audits/ch2-phase1-resolutions.md` and the three phase-1 findings files (the inherited obligations: output isolation, the round-3 split-search rejection pattern), `AroraBarakChapter2Plan.md`, `AroraBarakChapter1Plan.md`, `policy.md`; all 43 modules + root attached |
| Out of scope | everything certified at the phase-1 and Chapter-1 gates; the human-reserved design question 1; Exercise 2.6 (universal NDTM, deferred); phase-3/4 design questions |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.
