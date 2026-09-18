# External audit pack — Chapter 2, Phase 3 (formulas, SAT, TMSAT)

Audits commit `1a7554d1` on `complexity/arora-barak-ch1`. This is the **third
statement phase of the Chapter 2 campaign** (`AroraBarakChapter2Plan.md` §4),
opened after the phase-2 gate closed in one round
(`audits/ch2-phase2-resolutions.md`). The phase lands the CNF formula layer,
the languages `SAT`/`3SAT`, Lemma 2.14, and `TMSAT` with Theorem 2.9 — **16
definitions and 12 sorried statements, zero proofs** — across five new
modules. The product under audit is the statements, their conventions, and
their proof sketches. The gate closes on zero blockers/majors. Record findings
in `audits/ch2-phase3-findings.md`.

Source text: [AB09] §2.2 (Theorem 2.9 with footnote 2, pp. 43-44), §2.3.1
(CNF, `k`CNF, `SAT`, `3SAT`, footnote 3, pp. 44-45), Claim 2.13 (p. 46),
Lemma 2.14 with §2.3.5 (pp. 48, 50-51), §1.3 (time constructibility). [AB09]
Example 2.21 / `TAUTOLOGY` is **deliberately absent** — see priority 2.

## Repository-side attestations (maintainer, local machine — verify or challenge)

Per standing practice, source facts (verifiable from the bundle) are separated
from execution claims (maintainer-side; challenge their consistency, not their
reproduction).

1. **Freeze.** Commit `1a7554d1` touches exactly: five new Lean files
   (`Formulas/CNF.lean`, `Formulas/CNFEncoding.lean`, `Formulas.lean` facade,
   `ClassNP/SAT.lean`, `ClassNP/TMSAT.lean`), import/Contents additions in the
   `ClassNP` facade and the root `TCSlib.lean`, five inserted lines in
   `scripts/ab_ch1_module_order.txt` (now 48 modules — **attached this round**,
   per the phase-2 note disposition), and the plan (two decision rows, the §2/§4
   synchronization). Zero previously audited proof-bearing modules changed.
2. **Elaboration.** Full 48-module fresh-olean sweep, Lean 4.25.0 / mathlib
   `029db123ddaa`: zero `error:` lines, zero gate failures, exactly **45**
   `declaration uses 'sorry'` warnings — 19 phase-1 + 14 phase-2, both
   unchanged, plus exactly **12 new** (2 `Formulas/CNF` / 3
   `Formulas/CNFEncoding` / 3 `ClassNP/SAT` / 4 `ClassNP/TMSAT`).
3. **Admissions and axiom prints.** Tree-wide `sorry` count exactly 45, every
   admission under a **Proof sketch**. On the fresh tree: the eight Chapter-1
   headline prints remain `[propext, Classical.choice, Quot.sound]`; the new
   definitions print axiom-free (`Std.Sat.CNF.decode`, `Complexity.SAT`) or
   classical-only (`Complexity.TMSAT`); the new sorried statements show
   `sorryAx` as expected.
4. **Policy.** Style lint: zero FAIL over the campaign tree (the pre-campaign
   `NPReductions/*` legacy FAILs are outside the audited surface, untouched);
   the six Chapter-1 size WARNs unchanged. New files 147/209/23/153/200 lines.
5. **New surface inventory.** 16 definitions — 3 in the `Std.Sat.CNF`
   namespace layer (`Satisfiable`, `numVars`, `WidthAtMost`), 10 serialization
   (`serializeLit`, `serializeClause`, `serialize`, `takeTrues`, `parseLit`,
   `parseClause`, `parseClauses`, `parse`, `fallback`, `decode`), 3 in
   `Complexity` (`SAT`, `SAT3`, `TMSAT`) — and 12 sorried theorem signatures;
   **zero proofs** (unlike phase 2, nothing here mirrors proved
   infrastructure). One new external import: the Lean-core `Std.Sat.CNF`
   (toolchain-pinned; priority 1). The fuel-indexed parsers are total by
   structural recursion on fuel — no termination proofs, no `partial`, no
   `sorry` inside definitions.

## What is under audit

| Module | Definitions | Sorried statements |
|---|---|---|
| `Formulas/CNF.lean` | the carrier decision (`Std.Sat.CNF ℕ`); `Satisfiable`, `numVars` (one plus the largest mentioned index), `WidthAtMost` ([AB09]'s at-most-`k` `k`CNF) | `eval_congr_of_lt_numVars` (finite certificates determine evaluation), `exists_cnf_boolFun` ([AB09, Claim 2.13], clause-count/width rendering of the size measure) |
| `Formulas/CNFEncoding.lean` | the unary-index LL(1) grammar: serializers, `takeTrues`/`parseLit`/fuel-indexed `parseClause`/`parseClauses`, exact-consumption `parse`, `fallback = []`, total `decode` | `parse_serialize` (round trip), `decode_serialize`, `numVars_decode_le` (a decoded formula mentions at most `|x|` variables) |
| `ClassNP/SAT.lean` | `SAT`, `SAT3` (via total decoding; non-well-formed strings are members — fallback consequences recorded) | `SAT_mem_NP`, `SAT3_mem_NP` (parameters `(1,1)`, assignment certificates), `SAT_reducible_SAT3` ([AB09, Lemma 2.14], clause splitting) |
| `ClassNP/TMSAT.lean` | `TMSAT (c : MachineCode)` (right-nested `pairEncode` quadruple, unary `1^n`/`1^t`, `ComputesInTime … [true] t`) | `timeConstructible_poly` (**flagged**: a new statement about the Chapter-1 notion `TimeConstructible`, the `compl_mem_P` precedent), `TMSAT_mem_NP (c : EffectiveMachineCode)`, `TMSAT_NPHard (c : MachineCode)`, `TMSAT_NPComplete` ([AB09, Theorem 2.9]) |

## Brief for the auditor

Ground rules as always: closed gates (Chapter 1, phases 1-2) are trusted
context; textbook item numbers are the pack's citations; human-reserved
questions' dispositions are out of scope. Priorities:

1. **The seeded design question — the CNF carrier.** The provisional
   resolution adopts the Lean-core `Std.Sat.CNF ℕ` (a literal `(v, b)` is
   satisfied iff the assignment gives `v` the value `b`; empty formula `true`,
   empty clause `false`), with campaign additions extending the `Std.Sat.CNF`
   namespace, **unary variable indices** in the two-marker LL(1) serialization,
   exact-consumption parsing, and the **empty formula as fallback** ([AB09,
   footnote 3]). Assess: fidelity of the carrier's semantics to [AB09,
   §2.3.1]; the namespace-extension choice; whether unary indices lose
   anything any stated result needs (the recorded argument: only polynomiality
   matters and every consumer is polynomial-time); the fallback's
   consequences (every non-well-formed string in `SAT` and `3SAT`) against
   each stated theorem.
2. **The `TAUTOLOGY` deferral** (plan decision log): we claim the
   CNF-restricted tautology language is polynomial-time decidable (a CNF is a
   tautology iff every clause contains a complementary literal pair) and hence
   **not** [AB09]'s general-formula `TAUTOLOGY`, whose Example-2.21 reduction
   negates a CNF into a DNF; the package moves to phase 4 with the DNF dual
   layer. Verify the claim and the deferral's coherence — this was caught at
   drafting, and a second pair of eyes on it is exactly what this round is
   for.
3. **Adversarially re-derive the `TMSAT` statements.** (i) The definition
   against [AB09]'s: quadruple nesting, unary components, `u.length = n`,
   `ComputesInTime (pairEncode x u) [true] t`, and the membership existential's
   interaction with `pairEncode_injective` (can a string be a member "two
   ways"?). (ii) The generality split (`MachineCode` for the language and
   hardness, `EffectiveMachineCode` for membership) against the audited `HALT`
   precedent. (iii) The membership sketch's obligations — especially the two
   **discovered at drafting**: the unary-to-binary clock conversion
   (`Turing.timed_universal` takes `Nat.bits t`), and the **polynomial-in-`|α|`
   bound on the timed-universal constant** `C_α` (the statement provides it
   per-`α`; the verifier needs it uniformly — the sketch names deriving it from
   the `Universal` module's concrete bound definitions as a fill obligation;
   assess whether that is honestly derivable rather than wishful). (iv) The
   hardness sketch against the audited `HALT_NPHard` recipe: the wrapper
   machine, the normalization chain's total-function hypothesis, the explicit
   `T'` formula, and `timeConstructible_poly`'s role in the unary emissions.
4. **`SAT`/`3SAT` membership and Lemma 2.14.** The `(1,1)` certificate
   arithmetic against `numVars_decode_le`; the verifier obligations (odd-length
   split rejection, the parsing machine, unary-index evaluation walks,
   fallback-accept branches); the clause-splitting transform's
   equisatisfiability in both directions, fresh-variable bookkeeping via
   `numVars`, and the malformed-string case of the reduction equivalence
   (both sides true — check this is genuinely forced by the definitions).
5. **The serialization statements.** Is the LL(1) grammar as specified
   actually unambiguous (the clause-start `true` prefix vs. literal runs; the
   empty clause `[true, false]`)? Is fuel `x.length` genuinely adequate, and
   is that burden correctly assigned to `parse_serialize`'s proof rather than
   assumed? Is `numVars_decode_le`'s plain bound `|x|` right at the edges
   (empty string, bare `[false]`, fallback)?
6. **Claim 2.13's rendering** — the clause-count/width form of the size
   measure, the `Fin ℓ → Bool` function space, the restriction equation
   `φ.eval a = f (a ∘ Fin.val)`, and the `ℓ = 0` edge.
7. **`timeConstructible_poly`** as a statement: the `c + 1` exponent (the
   `T n ≥ n` constraint), `C > 0`, and its being stated here rather than by
   editing the frozen Chapter-1 file.

## Scope

| Item | Where |
|---|---|
| Files under audit | `Formulas/CNF.lean`, `Formulas/CNFEncoding.lean`, `Formulas.lean`, `ClassNP/SAT.lean`, `ClassNP/TMSAT.lean` (all new), the `ClassNP` facade and root `TCSlib.lean` diffs, the order-list insertion, the two plan decision rows |
| Context | `audits/ch2-phase{1,2}-resolutions.md` and the findings files (inherited obligations: output isolation, split rejection, relocated-and-captured simulation, the prefix-shaped bounded readings), both plans, `workflow.md`, `policy.md`, `scripts/ab_ch1_module_order.txt`; all 48 modules + root attached |
| Out of scope | everything certified at closed gates; Lemma 2.11 / Theorem 2.10 / the DNF layer / `TAUTOLOGY` (phase 4); the human-reserved design question 1; fill-time machine constructions beyond sketch-level obligation naming |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.
