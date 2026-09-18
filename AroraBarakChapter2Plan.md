# Formalization Plan: Arora-Barak Chapter 2 — NP and NP-completeness

Continuation of the Chapter 1 campaign (`AroraBarakChapter1Plan.md`, complete and
audited end to end), on the same branch `complexity/arora-barak-ch1`, under the same
methodology: audited statement phases with proof sketches, cross-vendor LLM audit
gates between phases, then a fill campaign in epochs of parallel disjoint-ownership
batches (zip delivery), verification through `scripts/lean_check_tree.sh` (**`lake
build` stays banned**), `scripts/style_lint.py` conformance, drift attestations
(ordered + multiset, per the epoch-4 methodology), and a blueprint-extraction
increment at closure. Audit artifacts are named `audits/ch2-phase*` /
`audits/ch2-epoch*`; briefs `briefs/ch2-*`.

## 1. Scope: what Chapter 2 contains

[AB09, ch. 2, pp. 38-67.] The mandatory core of this campaign:

* **§2.1** — `NP` via polynomial-time verifiers (Definition 2.1); Claim 2.4
  (`P ⊆ NP ⊆ EXP`); nondeterministic TMs, `NTIME`, and Theorem 2.6
  (`NP = ⋃ c, NTIME (n^c)`).
* **§2.2** — Karp reductions, `NP`-hardness/completeness (Definition 2.7);
  Theorem 2.8 (transitivity; the collapse consequences); Theorem 2.9 (`TMSAT` is
  `NP`-complete).
* **§2.3** — CNF formulas, `SAT`, `3SAT`; Claim 2.13 (CNF universality);
  **Theorem 2.10 (Cook-Levin)** via Lemma 2.11 (`SAT` is `NP`-hard, by the
  oblivious-machine tableau) and Lemma 2.14 (`SAT ≤ₚ 3SAT`).
* **§2.6** — `coNP` (Definitions 2.19/2.20 and their equivalence, Exercise 2.24),
  `EXP`/`NEXP`, Theorem 2.22 (`EXP ≠ NEXP → P ≠ NP`, padding); `TAUTOLOGY`
  `coNP`-complete (Example 2.21, once formulas exist).
* Selected exercises with structural value: 2.1 (bounded-length certificates),
  2.8 (`HALT` is `NP`-hard but not `NP`-complete — the bridge to Chapter 1),
  2.23 (`P ⊆ NP ∩ coNP`), 2.25 (`P = NP → NP = coNP`), 2.27 (`NEXP` without
  NDTMs).

**Deferred (phase-5-style, not scheduled):** §2.4's web of reductions (`INDSET`,
`0/1 IPROG`, `dHAMPATH`, and the exercise problems — each needs a graph/arithmetic
encoding surface; one exemplar may be pulled forward later to validate the
pattern, and the legacy `NPReductions/*` files may eventually be retargeted as the
structure-level halves); §2.5 decision-versus-search (Theorem 2.18); parsimonious
and Levin reductions (§2.3.6); the universal NDTM (Exercise 2.6 — Chapter 3's
tool); Berman's theorem (Exercise 2.30).

## 2. Foundation decisions

* **`NP` is verifier-first, language-level, with explicit length formulas**
  (as repaired by the phase-1 audit, finding 1): `L ∈ NP` iff there are a
  coefficient `C`, degree `c`, and a *language* `V ∈ P` with
  `x ∈ L ↔ ∃ u, |u| = C(|x|+1)^c ∧ x ++ u ∈ V`. The certificate length is
  always an explicit effective formula — never an abstract bounded function,
  which can smuggle undecidable information through length arithmetic
  (Argument A). Rendering the verifier as a `P`-language reuses the audited
  Chapter-1 class and was certified sound (finding 10). Concatenation is kept
  in the exact-length form: with the explicit formula, `n ↦ n + C(n+1)^c` is
  nondecreasing-plus-identity and the split is unique and computable wherever
  a consumer needs it (round-2 audit).
* **Certificates have exact length `C(|x|+1)^c`** (Definition 2.1, with the
  formula for [AB09]'s "polynomial `p`"); the bounded-length variant is
  Exercise 2.1, stated with **`pairEncode x u` pairing** on the bounded side
  (plain concatenation there forces `V ⊆ L` and collapses prefix-free
  languages — Argument B; a concatenation-based bounded variant is
  **equivalent to `P = NP`** and must never be stated, round-2 audit) and
  proved by padding to the admissible exact length `(C+1)(n+1)^c`.
* **NDTMs are binary-choice and functional** (phase 2): two total transition
  functions per [AB09] §2.1.2, semantics by a choice-word-indexed run function
  in the house `runFrom` style — *not* cslib's relational `MultiTapeNTM`
  (Papadimitriou-style arbitrary branching, `List`-chain semantics, stuck
  configurations), for the reasons recorded in the decision log. Acceptance is
  **output-based** (`[true]` on some choice word), consistent with
  `DecidesInTime`; `NTIME`'s totality bound quantifies over *all* choice words.
  Both are flagged as design questions for the phase-2 audit.
* **Poly-time computability of reduction functions is the recurring cost.**
  `Complexity.PolyTimeComputable` (FP) is defined in phase 1 together with its
  closure calculus (identity, composition — via the audited
  `computesFunInTime_comp` plus output-length bounds); further combinators
  (concatenation, constant prefixing, unary padding) are added in the phase that
  first needs them, never speculatively.
* **CNF formulas** (phase 3): the type, its evaluation, and its binary
  serialization with a parser and fallback totalization ([AB09] footnote 3 =
  the `codeFallback` convention). In-house type vs. `Std.Sat.CNF` is a recorded
  design question for the phase-3 audit.
* **Cook-Levin runs on our oblivious machines.** [AB09] proves Lemma 2.11 for
  oblivious *two-tape* machines and notes (footnote 5) the proof generalizes to
  any oblivious machine; `Complexity.oblivious_of_mem_DTIME` (quadratic,
  unrestricted tape count, oblivious on *all* inputs at every physical time) is
  the supply side. Snapshots have constant size `(state, k+1 symbols)`.

## 3. Architecture and module layout

New directory `TCSlib/Complexity/ClassNP/` (namespace `Complexity`), facade
`TCSlib/Complexity/ClassNP.lean`; later phases add `TCSlib/Complexity/Formulas/`
(or similar) for CNF and `NDTM` modules under `TuringMachine/`. Phase-1 layout:

| Module | Contents |
|---|---|
| `ClassNP/PolyTime.lean` | `PolyBound`, `PolyTimeComputable` (FP), identity/composition closure, output-length bound |
| `ClassNP/NP.lean` | `NP` (Definition 2.1, verifier-language form), `P ⊆ NP`, Exercise 2.1 |
| `ClassNP/CoNP.lean` | `coNP` (complement form), Definition 2.20 equivalence, `compl_mem_P`, Exercises 2.23/2.25 |
| `ClassNP/EXP.lean` | `EXP`, `ExpBound`, `NEXP` (Exercise-2.27 form), `P ⊆ EXP`, `NP ⊆ EXP`, `EXP ⊆ NEXP` |
| `ClassNP/Reductions.lean` | `PolyTimeReducible` (`≤ₚ`), `NPHard`, `NPComplete`, Theorem 2.8, downward closure of `P`, Exercise 2.8 (both halves) |

Chapter-1 files remain frozen at their audited surface; any addition to them is
flagged for audit per standing practice.

## 4. Phasing

Audit protocol as in Chapter 1 (`AroraBarakChapter1Plan.md` §5 "Audit protocol"):
each phase lands definitions plus sorried statements with policy-grade proof
sketches, an audit pack goes out, gates close on zero blockers/majors.

1. **Phase 1 — Classes and reductions** (this commit): the table above;
   ~14 sorried statements.
2. **Phase 2 — Nondeterminism**: raw binary-choice NDTM + choice-word semantics
   (`TuringMachine/Nondeterministic.lean`), `NTIME`, Theorem 2.6 (both
   directions as machine compilations), `NEXP` NTIME-form equivalence,
   Theorem 2.22 (padding).
3. **Phase 3 — Formulas, SAT, TMSAT**: CNF type + evaluation + serialization +
   parser/fallback; `SAT`, `3SAT`, membership in `NP`; Claim 2.13; Lemma 2.14
   statement; `TAUTOLOGY` + Example 2.21; `TMSAT` + Theorem 2.9 (supporting
   obligation: polynomial time-constructibility `n ↦ n^c`).
4. **Phase 4 — Cook-Levin**: snapshot/tableau layer over oblivious machines,
   the schedule-computability interface (head positions from a clocked
   simulation on a trivial input), Lemma 2.11, Theorem 2.10.
5. **Fill campaign**: scheduled after all gates close, epochs ordered by risk
   exactly as in Chapter 1 — (E1) assemblies + poly-calculus core, (E2) NDTM
   compilations + `NP ⊆ EXP` enumerator + padding + `TMSAT`, (E3)
   `SAT ≤ₚ 3SAT` machine + tableau correctness mathematics, (E4) the
   Cook-Levin reduction machine (the summit; B2-style continuation budget
   anticipated), (E5) closure: zero-sorry sweep, drift attestation, final audit
   pack, blueprint increment.

## 5. Risks and honest effort assessment

* **The Cook-Levin reduction machine is the summit** — a machine *emitting* the
  tableau formula clause-by-clause within a polynomial ledger, driven by the
  oblivious schedule. Larger than `universal` in my estimate; everything else is
  sequenced to de-risk it first.
* **Poly-time computability obligations recur** at every reduction; the
  mitigation is the phase-1 calculus plus need-driven combinators. A potential
  lever, recorded as an open option: upgrading `MathlibBridge` to preserve
  polynomial bounds (our `bridgeTM` costs O(1) native steps per TM2 statement
  operation, so a Mathlib `TM2ComputableInPolyTime` certificate would transfer)
  — an option, not a load-bearing assumption, since Mathlib supplies few such
  certificates.
* **Definition conventions are where audits bite** (the Argument-A lesson);
  the seeded design questions below go to the auditors *before* any fill.
* Estimated mandatory-core scale: ~35-45 audited sorries over four phases —
  larger than Chapter 1's 21, with one summit instead of two.

## Open design questions (human review required)

As in Chapter 1 (`AroraBarakChapter1Plan.md` §5), these are reserved for a
**human** decision; audit rounds verify correctness but do not dispose of them.

1. **Generality of `HALT_not_mem_NP`** (phase-1, round-2 audit, finding 3).
   The statement is currently at `Turing.EffectiveMachineCode` generality
   because its proof route reuses Chapter 1's `HALT_not_computable`, whose own
   proof runs the universal evaluator. The round-2 auditor showed this
   restriction is **not mathematically necessary**: a direct diagonalization —
   the public diagonal-pairing machine, the searcher's finite-control
   transform with the halt/loop roles swapped, `Turing.exists_codeTM`, no
   evaluator — proves `HALT` undecidable for *every* lawful
   `Turing.MachineCode` (and my earlier "trivial-machine scheme"
   counterexample is unlawful: constant decoding violates `decode_encode`).
   **The question:** add that diagonal lemma as a new audited statement (a
   strengthening of Chapter 1's uncomputability story that shares its main
   fill obligation, the control-transform lemma, with `HALT_NPHard`) and
   generalize `HALT_not_mem_NP` to `MachineCode` — or keep the conservative
   signature as a documented API/proof-route restriction? Maintainer's
   provisional choice, pending review: the conservative signature, with the
   docstring stating the restriction honestly; the diagonal lemma is
   deliberately *not* slipped into a repair round, since it would enlarge the
   audited surface of Chapter 1's uncomputability chapter.

## 6. Decision log

| Decision | Status |
|---|---|
| Chapter 2 proceeds on branch `complexity/arora-barak-ch1` (name notwithstanding), same methodology, gates, tooling, and delivery mechanics as Chapter 1; artifacts under `ch2-*` names | Decided |
| **Prior-art survey for NDTMs** (2026-09-18): Mathlib has none (nondeterminism stops at `NFA`/`EpsilonNFA`; TM0/1/2 deterministic). cslib — at our vendoring pin `a3747758` and unchanged on `main` — has `MultiTape/Nondeterministic.lean` (relational `MultiTapeNTM`, Papadimitriou §2.7 style, `List`-chain `ComputationPath` semantics, per-path exact-time notions, no acceptance, no all-branch time bound) and `MultiTape/DeterministicToNondeterministic.lean` (singleton-relation embedding). **Decision: do not port.** [AB09]'s binary-choice model is load-bearing for Theorem 2.6 (the certificate *is* the choice word; general relations have no canonical certificate encoding and admit stuck configurations), the campaign's proof style is functional (`runFrom` algebra — the original vendoring deliberately dropped cslib's relational semantics), and the port would drag in cslib's `IsChainFromTo` foundation plus new-module-system syntax. cslib's model is recorded as related work; a trivial embedding of our binary machine into their relational one is optional future upstream-reconciliation work | Decided |
| Vendored-file upstream drift check (2026-09-18): `Configuration.lean` and `Deterministic.lean` byte-identical upstream since pin `a3747758`; cslib's MultiTape directory has since grown (`TapeLemmas`, `ConfigBound`, combinators, `SingleTape/*`) — nothing needed now | Decided |
| `NP` defined verifier-first with the verifier as a language `V ∈ P` and exact-length concatenated certificates (`x ++ u`, no pairing) — splitting subtleties pushed to the concrete constructions that need them | **Superseded** (phase-1 audit, finding 1): the abstract length function was the defect; see the repair rows below and §2 |
| `EXP := ⋃ c, DTIME (2 ^ n ^ c)` ([AB09] Claim 2.4 verbatim); `NEXP` in Exercise-2.27 verifier form with `ExpBound` certificate lengths, NTIME-form equivalence deferred to phase 2 | `EXP` **Decided** (audit-confirmed); the `ExpBound` half **superseded** (finding 1) — `NEXP` uses the explicit formula `C·2^((n+1)^c)`; see the repair rows |
| Design questions seeded for the **phase-1 audit**: (a) the `V ∈ P` verifier rendering vs. explicit machines; (b) exact-length certificates as primary with Exercise 2.1 as the bridge; (c) `PolyBound`'s `C·(n+1)^c` normal form; (d) `Complexity.compl_mem_P` as a new statement on Chapter-1 classes (addition beyond the audited ch-1 surface, flagged); (e) the `≤ₚ` notation scope | Open — to auditors |
| Design questions seeded for the **phase-2 audit**: (a) output-based acceptance (`[true]` on some choice word) vs. a literal `qaccept` state — [AB09] deviation to be justified or reversed; (b) `NTIME`'s all-branch halting bound quantifier placement; (c) choice words as `List Bool` vs. `ℕ → Bool` | Open — to auditors |
| Design question seeded for the **phase-3 audit**: in-house CNF type vs. `Std.Sat.CNF`; serialization scheme and fallback convention | Open — to auditors |
| §2.4 web of reductions, §2.5 search-to-decision, parsimonious/Levin reductions, Exercise 2.6 (universal NDTM), Berman's theorem: **deferred**, not scheduled in the mandatory core | Decided |
| `MathlibBridge` poly-time upgrade as an optional lever for reduction machines | Open — revisit at phase 3 |
| Phase-1 audit round 2 (`audits/ch2-phase1-reaudit-findings.md`): **zero blockers, 3 majors, 2 minors, 2 notes — gate stays open, but the round-1 repairs are certified**: Arguments A, B, D re-fired against the repaired definitions and confirmed dead; "no false Lean theorem statement"; resolution table verified row by row; all 19 statements assessed sound; `pairEncode x u` order confirmed; a concatenation-based bounded Exercise-2.1 variant shown **equivalent to `P = NP`** (never to be stated). Majors, all sketch/prose-level: (1) the Ex-2.1 reverse witness `C(n+1)^c + 1` is not of the class's admissible shape — corrected construction `R n = (C+1)(n+1)^c` supplied with edge-case table and ~8,000 executable checks; (2) the enumerator obligations omitted **output isolation** (append-only output means resets cannot un-emit; round 1's buffering requirement had been dropped); (3) the "effectivity is necessary" justification for `HALT_not_mem_NP` is false — the trivial-machine scheme violates `decode_encode`, and a direct diagonalization proves `HALT` undecidable for every lawful `MachineCode`. Minors: plan §2 prose stale; pack attestation-3 count mixed categories (erratum acknowledged, pack preserved per precedent) | Decided |
| Round-2 repairs executed (sketch/prose only — **no statement changed**): Ex-2.1 reverse sketch adopts the auditor's `R n = (C+1)(n+1)^c` construction; the enumerator sketch gains the verifier-call capture obligation (suppress emissions, capture the bit in control, redirect the halt; `universalCaptureTM` as in-repo precedent; reset includes heads, control, and the captured bit); `HALT_not_mem_NP`'s docstring restated as a **proof-route restriction** with the unlawful-counterexample retraction and a pointer to the new human-review question; plan §2 synchronized and the two superseded decision rows marked. The `MachineCode`-generalization decision is recorded under "Open design questions (human review required)", question 1 — provisional maintainer choice: keep the conservative signature; do not grow the audited uncomputability surface inside a repair round. All repaired modules re-gated clean; 19 admissions unchanged; lint unchanged. **Round-3 re-audit next** (protocol: no gate closes on a round reporting majors) | Decided |
| Phase-1 audit round 3 (`audits/ch2-phase1-round3-findings.md`): **zero blockers, zero majors, one minor, two notes — gate condition met.** Resolution table verified row by row; the adopted Exercise-2.1 construction independently reconstructed with a six-step derivation and seven edge cases; the enumerator obligation list judged complete at statement phase, with a contract-by-contract fill table (to be inherited verbatim by the eventual fill brief); the HALT proof-route framing confirmed accurate. Minor swept in the closing commit: the split search's explicit no-solution rejection branch (comment-only, verified, re-gated). **Phase-1 audit gate closed** (`audits/ch2-phase1-resolutions.md`) — 10 definitions + 19 statements audited through three adversarial rounds. Next: phase-2 skeleton (nondeterminism) | Decided |
| Phase-1 skeleton landed (`ab82bb6a`): 10 definitions + 19 sorried statements + 1 scoped notation across the five `ClassNP/` modules and facade, every statement with a policy-grade sketch; gate-verified per module and by a **full 40-module fresh sweep** (zero errors; exactly the 19 admissions, all in `ClassNP/`); Chapter-1 freeze verified by path enumeration; the eight Chapter-1 headline axiom prints remain admission-free on the fresh tree; style lint zero FAIL. **Phase-1 audit pack prepared** (`audits/ch2-phase1-{pack,bundle}.md`) with the seeded design questions (a)-(e) as auditor priorities, including the Exercise-2.1 marker-free-tail trap found at drafting. Gate awaits `audits/ch2-phase1-findings.md` | Decided |
| Phase-1 audit round 1 (`audits/ch2-phase1-findings.md`): **3 blockers, 3 majors, 3 minors, 3 notes — gate stays open; all accepted.** The chapter-2 Argument A: `PolyBound p` constrains the certificate-length function only numerically, so length *arithmetic* smuggles undecidable information (`p_A(n) ∈ {2n, 2n+1}` against a mod-3 verifier decides any `A`) — the pre-repair `NP`/`NEXP` contained undecidable languages, `NP ⊆ EXP` and `HALT_NPHard` were false (the latter vacuously: Argument D shows *nothing* was NP-hard for that class), and the Exercise-2.1 equivalence was doubly false (Argument B: bounded-length + plain concatenation forces `V ⊆ L`, collapsing prefix-free languages — an obstruction that survives the length repair, so the bounded form needs pairing). The `V ∈ P` verifier abstraction itself was **certified sound** (finding 10: "the oracle is the unconstrained `p`, not `V`") | Decided |
| Phase-1 repairs executed per the audit's own proposals: `NP`, `coNP`'s ∀-characterization, and `NEXP` now quantify over **explicit effective length formulas** — exactly `C·(n+1)^c` (resp. `C·2^((n+1)^c)`) certificate bits, never an abstract function; `PolyBound`/`ExpBound` demoted to numerical helpers with corrected docstrings; Exercise 2.1 restated with `pairEncode x u` pairing on the bounded side and a split-then-strip verifier checking the *original* explicit bound (the audit's residual-soundness fix); `NP ⊆ EXP` re-sketched with the polynomial-evaluation, fixed-width-counter, retention/reset, and timed-loop obligations named (finding 5; private `counterInc` acknowledged as template, not API); `compl_mem_P` and `mem_P_of_polyTimeReducible` re-sketched through the timed `computesFunInTime_comp` (finding 4); `HALT_NPHard` **generalized to every `Turing.MachineCode`** (finding 11) with the audit's total-decider-then-loop-on-rejection searcher recipe (finding 6) and the fixed-prefix `pairEncode α ·` machine obligation; `HALT_not_mem_NP` stays at `EffectiveMachineCode` with the pathological-scheme justification recorded; composition degree `max c (c·c')` (finding 7); monotonicity attributions fixed (finding 8); stale names fixed (finding 9); **root `TCSlib.lean` now exports the `ClassNP` facade** (note 12 — a genuine miss). All six modules re-gated clean, same 19 admissions, lint unchanged. **Re-audit round 2 required before any fill** (the Chapter-1 phase-3 precedent) | Decided |

| Phase-2 skeleton landed (`e1e68ebd`): binary-choice NDTM with `List Bool` choice-word `runWith` semantics, all-branch `HaltsWithin`, bundled `FinNDTM`, and the deterministic embedding (`TuringMachine/Nondeterministic.lean`); output-based `AcceptsWithin`/`DecidesInTime` and the classes `NTIME` (`ClassNP/NTIME.lean`); both directions of Theorem 2.6, the `NTIME` form of `NEXP` (the Exercise-2.27 reconciliation), and Theorem 2.22 through the certificate route (`ClassNP/Nondeterminism.lean`). 11 definitions + 14 sorried statements with policy-grade sketches + **6 proved definitional-unfolding lemmas** (the `runWith` algebra — a deliberate, flagged deviation from the phase-1 zero-proof convention, mirroring the vendored `runFrom` lemmas of `Deterministic.lean`; their proofs are part of the audited surface). Gate-verified per module and by a full **43-module fresh sweep** (zero errors; exactly 33 admissions = the 19 phase-1 ones unchanged + 2/4/8 new); the only touches to previously audited files are the two facade import/Contents additions and the order-list insertion (path enumeration); the eight Chapter-1 headline axiom prints remain admission-free on the fresh tree; style lint zero campaign FAIL. **Phase-2 audit pack prepared** (`audits/ch2-phase2-{pack,bundle}.md`) carrying seeded questions (a)-(c) plus the drafting-time questions: (d) exact-length choice-word quantifiers with monotonicity lemmas, (e) the `+ 1`-padded polynomial `NTIME` union mirroring `P`, (f) Theorem 2.22 via the certificate form rather than [AB09]'s NTIME-machine padding. Gate awaits `audits/ch2-phase2-findings.md` | Decided |

| Phase-2 audit round 1 (`audits/ch2-phase2-findings.md`, audited at `e1e68ebd`): **zero blockers, zero majors, 2 minors, 2 notes — gate condition met on the first round.** All 11 definitions blind-restated and assessed faithful; all 14 statements assessed sound, with the four compilation directions and the padding theorem adversarially reconstructed (shape inequalities at every degree, unique-split strict increase, the simulator invariant table, guess-phase witness coverage/extraction, budget envelopes, small-length absorption); the six proved lemmas' proof terms checked; design questions (a)-(f) all resolved in favor of the chosen conventions. Minors, both prose: (1) the Theorem-2.22 sketch's binary-length estimate for `E |x|` used validity before checking it — repaired with the pre-validation uniform bound `(n+1)^c + bits(C) + 1`; (2) the exact-vs-bounded interchangeability prose overbroad — the bounded all-branch reading is prefix-shaped, not "all shorter words halted". Notes adopted: the obligation tables are inherited verbatim into the phase-2 fill briefs; future bundles attach `scripts/ab_ch1_module_order.txt`. **Minors swept in the closing commit (comment-only, verified; modules and facades re-gated, admissions unchanged); phase-2 gate closed** (`audits/ch2-phase2-resolutions.md`). Next: phase-3 skeleton (CNF formulas, SAT, TMSAT) | Decided |

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Ch. 2, pp. 38-67.)
