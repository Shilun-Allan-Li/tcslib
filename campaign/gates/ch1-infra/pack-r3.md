# External audit pack — shared infrastructure round, round 3

Repair round for `audits/ch1-infra-r2-findings.md` (round 2: **0 blockers,
1 major, 3 minors** — gate OPEN). Round 2 passed the redesigned loop
statements, P13/P14/C1, the §9b instantiation tables, and the corrected
evidence, and formally discharged both round-1 refutations; its single
major is an interface-shape gap, repaired here by exporting the
configuration-level loop contract. The round-2 attack commentary's two
qualifications and all three minors are also adopted. Gate closes on zero
blockers/majors. Record findings in `audits/ch1-infra-r3-findings.md`.

## Resolution table (round-2 findings → repairs)

| # | Finding | Resolution |
|---|---|---|
| 1 | **Major** — the loop's final-answer conclusion cannot discharge `enumMachine_contracts` (the delay-machine separation) | **Repaired** (`Build/Loop.lean`): new `exists_loopCfgTM`, same hypotheses as the decision form, concluding with the host's **round-configuration family** — startup ≤ `c·(T+1)` reaching `cfg 0`; empty output at rounds `0…R`; per-round accept-or-advance segments each within `c·(T+1)` (acceptance halts `[true]`, advance reaches `cfg (i+1)`); halted `[false]` terminal at index `R+1`. The delay machine fails the per-round clauses, closing the separation. The decision form's docstring now records it as a fill-time corollary (`loop_run` + monotonicity). The index/budget translation to `enumMachine_contracts` is recorded in `machine-library-design.md` §9c: `2^w = R n + 1` aligns the terminal index; `b·(n+w+1)^e` dominates `c·(T n + 1)` for `T` polynomial in `n + w`; the per-round indicator matches via the fill's orbit bridge `(stepF x)^[i] (s0 x) = enumWord w i`. |
| 2 | Minor — lint attestation described one invocation | **Erratum acknowledged; restated below** (attestation 6) with both invocations and the recorded escalations covering all seven WARNs. |
| 3 | Minor — "standard triple" overstated the Convention prints | **Erratum acknowledged; restated below** (attestation 2): axiom sets are *subsets of* the standard triple; the exact prints are `[propext, Quot.sound]` and `[propext]`. |
| 4 | Minor — P10's intro still named the Boolean loop | **Repaired**: the introductory reference now names `exists_loopFindTM` with the reason. |
| 5 | Note — vocabulary equal only with the coefficient shift | **Adopted** (§9c): `solveSplit (C+1) c = certificateSplit C c`; the padded-verifier pipeline uses P10 at `(C+1, c)` and P8 at `(C, c)`. No unqualified same-parameter equality is recorded anywhere. |
| 6 | Note — residual evidence limits | **Supplied where decidable**: `audits/evidence/ch1-infra/tree-deltas.txt` gives the whole-Lean-tree C→D and D→E diffs (Build files only) and proves by git blob identity that the **current** `Universal.lean` and `TMSAT.lean` are byte-identical to their audited post-export state (`f6bfefbf…` / `8492aea5…` — the latter matching the auditor's own item-11 recomputation); the run-C sweep log is attached this round. The E3/E4 brief-level coverage is **withdrawn from D5's scope** (§9c): those rows are component-level plausibility, finalized at the E3/E4 brief audits where the six-stage/boundary/ledger tables are in scope. Toolchain/fresh-olean execution remain execution attestations, as before. |
| — | Item 7's two commentary corrections (`q₀ = anchor` with `body.k = 0`; noncomputable `acceptF` off-invariant) | **Adopted**: the pack commentary was too broad; the loop statements themselves were unaffected. This pack carries no replacement blanket claims. |
| — | Item 6's line-count correction | **Erratum acknowledged**: the immediate pre-export `Universal.lean` had 2,834 lines (the round-1 pack's "2831 → 2901" used the epoch-4A historical figure as the immediate baseline). |
| — | Item 10's D-MEM caveat (C1 cannot cross components) | **Adopted** (§9c): cross-component operations go through the retained-whole-request pattern; the audit's explicit `H/s/t` pairing derivation is recorded verbatim as the canonical assembly recipe. |

## Corrected and extended maintainer attestations (verify or challenge)

1. **Elaboration.** Run E (`audits/logs/ch1-infra-r3-sweep.log`): full
   fresh-olean 57-module sweep at the repair state, zero `error:` lines,
   exactly **51** admission warnings — 23 in Build (4 wrapper, 4 loop, 15
   primitive) and 28 elsewhere. Runs A/B/C/D as before (47/46/46/50);
   run C's log is attached this round.
2. **Axioms.** `audits/logs/ch1-infra-r3-axioms.log`, from the two
   committed programs (the Build program now prints 23 contracts):
   exactly **26** `sorryAx` prints — the 23 Build contracts and the three
   TMSAT D-site targets. The five Chapter-1 headlines, the export, and
   the discharged bridge print the standard triple; the two Convention
   lemmas print **subsets** of it (`[propext, Quot.sound]`; `[propext]`);
   the root-traversal assertions pass unchanged.
3. **Scope of this round.** `tree-deltas.txt`: the only Lean sources
   changed since run D are `Build/Loop.lean` (the configuration export)
   and `Build/Primitives.lean` (the P10 reference fix); and the current
   bridge-side files are git-blob-identical to their audited state.
4. **Statement stability.** The round-2-passed statements —
   `exists_loopTM`, `exists_loopFindTM`, P13/P14/C1, and all earlier
   contracts — are byte-unchanged this round except the two documented
   docstring touches (the decision form's corollary note; P10's intro);
   `exists_loopCfgTM` is the only new declaration.
5. **Topology** (as restated in round 2, unchanged): outside the Build
   subgraph, the only direct importer of any Build module is the facade.
6. **Policy** (restated per round-2 finding 2). Full lint
   (`audits/logs/ch1-infra-r3-lint.log`), both invocations: **0 FAIL,
   7 WARN over 38 files** — six machine-tree size WARNs plus
   `TMSAT.lean`. All seven sit under recorded escalations: `Universal`
   (epoch-4A row: the brief forbade splitting; ~1,100 lines are
   stopped-interpreter administrative copies forced by per-module `match`
   auxiliaries), `TMSAT` (ch2 epoch-2 checkpoint row: single-file fill
   ownership), and the five merge-refactor files (`MathlibBridge`,
   `Oblivious`, `ObliviousCandidate`, `ObliviousSetup`,
   `UniversalInterpreter` — epoch-3→4 merge row: "five files remain at
   1020–1147 lines, justified: Interpreter/Block cut fixed by matcher
   identity, ObliviousCandidate/Setup/residual bounded by
   interleaved-layer seams, MathlibBridge kept whole as the single
   foreign-trust quarantine").

## D5, version 3 (approve or challenge)

Scope: the epoch-2 frontiers and P10. E3/E4 rows are withdrawn to their
own brief audits (§9c). Updates over round 2's table, incorporating the
round-2 dispositions:

| Customer | Disposition requested |
|---|---|
| 2A `enumMachine_contracts` | **Now via `exists_loopCfgTM`** at the §9b instantiation, with the §9c index/budget translation and the orbit bridge as fill obligations. |
| P10 / split search | Covered (round-2 item 8); the intro reference is fixed. |
| 2C `pairedVerifier` | Per round-2 item 10: the exact-width test is both orientations of P8 via the recorded pairing derivation, conjoined. |
| 2C `paddedVerifier` | P10 at **`(C+1, c)`**, strip, P8 at `(C, c)`, guards before the old verifier — the coefficient shift of round-2 note 5. |
| D-WRAP | Covered: guarded P13 + verifier composition (round-2 item 10). |
| D-EMIT | Covered: the §9c canonical pairing derivation applied to the two exact P5 unary outputs, then the retained input and the fixed outer encoder (round-2 item 10's explicit construction). |
| D-MEM | Dynamic assembly supported (derivation above); the remaining parser/body obligations (timed `w.take n` extraction from the parsed unary clock, unary-shape checks, the complete-answer test) are **named fill obligations of the D-MEM continuation**, not claimed library consequences. |
| 2B `choiceVerifier` | As round 2: P10 split + the batch's proved simulation core as body + guards + glue; the NDTM-side reverse direction remains bespoke by design. |
| Clearing | Internal; each rejected body round owes its concrete scratch-restoration proof at fill time — the §3 policy sentence is the discipline, not the proof. |

## What is under audit, round 3

1. **`exists_loopCfgTM`** — the only new statement. Truth and
   realizability: re-derive that the intended host (the round-2 item-7
   construction, read at segment granularity) supplies the configuration
   family; attack the per-round uniform bound `c·(T+1)` (counter debits
   at round boundaries, the underflow-plus-emission advance into the
   terminal, empty-output clauses); check the delay-machine separation is
   actually closed; and verify the §9c translation really lands on the
   attached, unchanged `enumMachine_contracts` (`EXP.lean`), including
   the terminal index `2^w = R + 1` and the budget domination.
2. **The two docstring touches and §9c** — consistency; no statement
   drift (attestation 4).
3. **The corrected attestations** (lint totals with the quoted
   escalations; the Convention subset wording; the 2,834 baseline; the
   new tree-delta/blob evidence).
4. **D5 v3** — approve per row, or name the specific residual gap.

Unchanged and not re-audited: everything round 2 passed (both final-answer
loops, P13/P14/C1, the 15 earlier contracts, `loop_run`, Convention, the
bridge proofs, the model files), except as listed in attestation 4.
Severity scheme as always; findings to `audits/ch1-infra-r3-findings.md`;
this pack is immutable once sent.

## Verification appendix (runs and manifest)

* Runs A–D: as attested in round 2 and verified by its item 11 (A: 47,
  B: 46, C: 46, D: 50 admissions; all 57/57, zero errors).
* Run E — `audits/logs/ch1-infra-r3-sweep.log` (attached): 57/57, 0
  errors, 51 admissions, at the repair state under audit.
* Axioms — `audits/logs/ch1-infra-r3-axioms.log` (attached): 26 `sorryAx`
  prints exactly; traversal PASS; exit 0.
* Lint — `audits/logs/ch1-infra-r3-lint.log` (attached): 0 FAIL, 7
  pre-escalated WARNs over 38 files, both invocations reported.
* Bundle manifest — **26 attachments** after the pack: the round-2 and
  round-1 findings and the round-2 pack (3); the 4 Build modules, the
  design document, the model base (`Configuration.lean`,
  `Deterministic.lean`, `Finite.lean`, `Simulation.lean`),
  `Composition.lean`, `Encoding.lean`, `EXP.lean` (the frozen customer
  contract), `NP.lean`, the facade, and the order list (15); the 2
  evidence files this round cites (`tree-deltas.txt`,
  `byte-attestation.txt`); the 2 committed programs; the 4 logs — runs C
  and E, the round-3 axioms, and the round-3 lint
  (3 + 15 + 2 + 2 + 4 = 26). The round-2 bundle remains the reference
  for the remaining unchanged files and evidence not re-cited here.
