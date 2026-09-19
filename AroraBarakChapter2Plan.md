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
  design question for the phase-3 audit. Provisional resolution (2026-09-18,
  decision log): the carrier is the Lean-core `Std.Sat.CNF ℕ`; serialization
  uses unary variable indices in an LL(1) marker grammar; the fallback is the
  empty formula.
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
   statement; `TMSAT` + Theorem 2.9 (supporting obligation: polynomial
   time-constructibility). `TAUTOLOGY` + Example 2.21 **moved to phase 4**
   (decision log: the faithful carrier is the DNF dual, and the hardness half
   needs Lemma 2.11).
4. **Phase 4 — Cook-Levin**: snapshot/tableau layer over oblivious machines,
   the schedule-computability interface (head positions from a clocked
   simulation on a trivial input), Lemma 2.11, Theorem 2.10; the DNF dual
   layer with `TAUTOLOGY` + Example 2.21.
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
**human** decision; audit rounds verify correctness but do not dispose of
them. **The full question statements live in [`backlog.md`](backlog.md) §1**
(the consolidated tracking file, 2026-09-18); the stable numbering below is
what audit documents cite.

1. **CH2-Q1 — generality of `HALT_not_mem_NP`** (phase-1, round-2 audit,
   finding 3): the round-2 auditor showed the `EffectiveMachineCode`
   restriction is a proof-route artifact, with a direct diagonalization
   available at every lawful `MachineCode`. The question: state that
   diagonal lemma and generalize, or keep the conservative signature as a
   documented restriction? Provisional maintainer choice: the conservative
   signature. Full statement: `backlog.md` §1, CH2-Q1.

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

| **CNF carrier prior-art decision** (2026-09-18): adopt the Lean-core `Std.Sat.CNF ℕ` — `List (List (ℕ × Bool))` with `eval` an all/any nest, literal `(v, b)` satisfied iff the assignment gives `v` the value `b` — as the formula type, instead of an in-house duplicate. Rationale: the in-house candidate would have been byte-for-byte this shape; core supplies `eval`'s simp set, the mentioned-variable machinery (`Mem`, `eval_congr`) and `relabel`/`eval_relabel` (the fresh-variable tools Lemma 2.14 and the tableau want); policy prefers the existing mechanism. Campaign formula-level additions (`Satisfiable`, `numVars`, `WidthAtMost`, serialization) extend the `Std.Sat.CNF` namespace; complexity-level definitions stay in `Complexity`. Risks accepted and recorded: upstream namespace evolution at future toolchain bumps; the abbrev-based `Literal` (no named fields). Serialization: **unary variable indices** in an LL(1) two-marker grammar (parser-machine simplicity; the polynomial size loss is immaterial — every consumer is polynomial-time), exact-consumption parsing, fallback = the empty formula. Provisional, **to the phase-3 auditors** with the seeded question | Decided |
| **`TAUTOLOGY` + Example 2.21 moved to phase 4** (2026-09-18, caught at phase-3 drafting): [AB09]'s `TAUTOLOGY` ranges over general Boolean formulas, and Example 2.21's reduction negates the Cook-Levin CNF into a **DNF** — while the CNF-restricted tautology language is polynomial-time decidable (a CNF is a tautology iff every clause contains a complementary literal pair), i.e. **not** [AB09]'s language. The faithful carrier (a DNF dual layer with the literal-negating `CNF → DNF` map) and the hardness half's prerequisite (Lemma 2.11) both belong to phase 4, so the package moves there; phase 3 states nothing about tautologies rather than stating a wrong-language definition | Decided |

| Phase-3 skeleton landed (`1a7554d1`): the CNF layer over `Std.Sat.CNF ℕ` (`Satisfiable`/`numVars`/`WidthAtMost`, Claim 2.13) and the unary-index LL(1) serialization with exact-consumption fuel parser and empty-formula fallback (`Formulas/{CNF,CNFEncoding}.lean` + facade); `SAT`/`SAT3` with `NP` memberships and Lemma 2.14 (`ClassNP/SAT.lean`); `TMSAT` with the `HALT`-style generality split, Theorem 2.9 in three statements, and the **flagged** `timeConstructible_poly` statement on the Chapter-1 notion (`ClassNP/TMSAT.lean`). 16 definitions + 12 sorried statements, zero proofs; full **48-module fresh sweep** clean (exactly 45 admissions = 19 + 14 + 12); the eight Chapter-1 headline axiom prints admission-free; new external import `Std.Sat.CNF` (toolchain-pinned); root `TCSlib.lean` exports the `Formulas` facade; style lint zero campaign FAIL. **Phase-3 audit pack prepared** (`audits/ch2-phase3-{pack,bundle}.md`; the bundle now attaches `scripts/ab_ch1_module_order.txt`, per the phase-2 note disposition) with the carrier/serialization/fallback design question, the `TAUTOLOGY` deferral verification, and the two drafting-time `TMSAT` obligations (unary-to-binary clock conversion; the polynomial-in-`|α|` bound on the timed-universal constant) as priorities. Gate awaits `audits/ch2-phase3-findings.md` | Decided |

| Phase-3 audit round 1 (`audits/ch2-phase3-findings.md`, audited at `1a7554d1`): **2 blockers, 1 major, 2 minors, 3 notes — gate stays open; all accepted.** The blockers share one obstruction, the chapter's third Argument A: `Turing.EffectiveMachineCode` constrains the canonizer's *computability* but not its *cost*, and a lawful effective scheme (the base scheme behind a one-bit tag, tagged codes decoding to one-step machines that emit bits of a diagonal decidable language `A ∉ EXP`) makes its `TMSAT` decide `A` on trivial instances — so `TMSAT_mem_NP` and `TMSAT_NPComplete` were **false at their stated generality**: the universally quantified statements refuted by one lawful scheme, via the audited `NP ⊆ EXP` (quantifier wording corrected per round-2 finding 2). The auditor also refuted the drafted hope of bounding the universal constant "by inspection" (it contains `canonizerTime`) and supplied the quantified sufficient repair — `C_α ≤ 3r + 14H + 50`, so `PolyBound c.canonizerTime` restores a uniform budget — with the caveat that the fill needs a **new public quantitative bridge** in the `Universal` module. Major: the hardness sketch's unary emissions — the exact certificate length `Q` is not time-constructible in degenerate cases and **must not be majorized** (explicit false positive at `C₀ = c₀ = 0`); corrected case table and explicit deadline `T' n = D(n+1)^(2er)` supplied. Minors: a parity flip in the membership split rejection (well-formed verifier inputs are odd); the fallback-independence prose overbroad. Notes: all 16 definitions and the other ten statements confirmed (grammar, fuel adequacy, and the `numVars` bound verified with ~262k executable parser checks on the auditor's side); the `TAUTOLOGY` deferral **independently proven justified** (complementary-pair criterion derived), with phase-4 guidance to present the DNF rendering as a fragment; attestation accounting consistent | Decided |
| Phase-3 round-1 repairs executed (**phase 3's two statement-level repairs** — the campaign's earlier statement repairs were phase 1's round-1 set; wording corrected per round-2 finding 1): `TMSAT_mem_NP` and `TMSAT_NPComplete` now carry `(hc : PolyBound c.canonizerTime)` — the auditor's minimal option: no new code interface, Chapter-1 freeze preserved, `TMSAT` and `TMSAT_NPHard` untouched at their audited generality. The membership sketch gains the Argument-A rationale, the corrected **even-length** rejection, the quantified budget chain, and the named **new-public-bridge obligation** (a quantitative form of `timed_universal`'s constant; `Universal`-surface growth to be requested through the shared-file mechanism and flagged at its own audit — a prose obligation alone cannot discharge the budget). The hardness sketch adopts the exact-value emission case table (`C₀ = 0` / `c₀ = 0` / general) and the auditor's explicit `T'` formula, majorizing only the deadline. `SAT.lean`'s fallback prose corrected per finding 5. Statement drift enumerated: exactly **2 signatures changed** (hypothesis additions), 0 definitions, one precise import added; `SAT.lean` comment-only (comment-stripped diff). **Erratum, disclosed**: the comment-only verifications of the phase-2 closing sweep and this round's first check had run the comment stripper with a vacuous invocation (a stdin-reading script given a filename argument, producing empty output on both sides); re-run correctly, every previously attested claim is confirmed — the phase-2 closure files are comment-stripped identical across `e1e68ebd..487f58cb` — and the corrected recipe is recorded here. Repaired modules and facade re-gated; tree admissions unchanged at 45. **Round-2 re-audit next** (protocol: no gate closes on a round reporting blockers) | Decided |

| Phase-3 audit round 2 (`audits/ch2-phase3-reaudit-findings.md`, audited at `8b09a184`): **zero blockers, zero majors, 2 minors, 2 notes — gate condition met.** Resolution table verified row by row; both signature repairs judged sufficient, the budget chain independently re-derived from the `Universal` module's concrete definitions (every size inequality traced to the serialization format); an exhaustive argument that no other phase-3 statement needs the canonizer hypothesis; Derivation B confirmed with no off-by-one (43,680 deadline-parameter checks); parity and fallback repairs confirmed; the hypothesis characterized as sufficient-but-not-weakest (consistent with the statements, which claim sufficiency only). Minors, both audit-history prose: "chapter's first statement-level repairs" (phase 1's round 1 already repaired statements) and the "false at every scheme" quantifier slip — **both corrected in the closing commit**; the shipped round-2 pack's identical phrase acknowledged as an erratum, pack preserved. Notes adopted: the fill's public bridge pinned to one pre-chosen simulator with both `timed_universal` clauses (suggested form avoids importing `PolyBound` into Chapter 1); the stripper-erratum reproducibility appendix (exact command, script hash, refs, nonempty counts, output hashes) added to `audits/ch2-phase3-resolutions.md`. **Phase-3 audit gate closed** — 16 definitions + 12 statements audited through two adversarial rounds. Next: phase-4 skeleton (Cook-Levin + the DNF/TAUTOLOGY package) | Decided |

| **Prior-art survey for Cook-Levin** (2026-09-18): reviewed two user-supplied files produced by OpenAI's Astra — `ThreeSATNPHardness.lean` (58,406 lines, **sorry-free**, `import Mathlib`: a kernel-checked proof of `paperOriginalThreeSATIsNPHard`, i.e. Cook-Levin through 3SAT, mechanically extracted as the dependency cone of a larger `GapCVP.lean`; NP defined over Mathlib's TM2 stack-machine framework `Turing.TM2ComputableInPolyTime` with `Polynomial ℕ`-bounded certificates and Bool-valued languages via `Classical.propDecidable`; the proof constructs a TM2 machine emitting the tableau as an explicit 3CNF word with proved polynomial running time) and `H_GapCVP.lean` (a sorried GapCVP/nearest-codeword promise-problem harness, outside ch-2 scope). **Decision: not adopted.** Reasons: (i) model mismatch — TM2 vs our audited multi-tape surface; a time-bound-preserving bidirectional bridge (Mathlib's own TM reductions are semantics-only) plus NP-equivalence and re-encoding layers would rival the native construction in effort while permanently importing a foreign trusted surface; (ii) convention mismatch at every joint (their bounded-certificate Bool-language NP, exactly-3 clauses, different encodings vs our audited explicit-length set-language NP and width-≤-3 `Std.Sat.CNF ℕ`); (iii) un-auditable under our protocol — a machine-extracted cone with bare `import Mathlib`, no attribution or sketches, cannot pass the blind-restatement discipline; provenance/license unstated. **Retained**: their `CL` namespace's factoring (abstract tableau spec + trace correctness, separated from the emitting machine) as a design reference — echoed in our `Snapshot`/`Hardness` split; and the ~55k-line scale as corroboration of the E4 summit estimate | Decided |
| Design questions seeded for the **phase-4 audit**: (a) the acceptance clause family "no step emits `false`" replacing [AB09]'s condition 4 under the output convention — its reliance on the decider contract for the at-least-one-emission half; (b) `prevVisit = none` reads blank vs [AB09]'s footnote-6 `prev(i) = 1` convention; (c) positions-only obliviousness — a common budget horizon instead of [AB09]'s common halting time, with halted branches in every reconstruction function; (d) the certificate as free input variables with `x` pinned by unit clauses (Example 2.12's rendering degenerating on constants); (e) `TAUTOLOGY` as the documented DNF-fragment rendering over the shared serialization (round-1 finding-7 guidance), with the fallback flipping sides; (f) `coNPHard`/`coNPComplete` as new definitions on audited notions | Open — to auditors |

| Phase-4 skeleton landed (`6484ce88`): the DNF dual layer on the shared carrier (`Formulas/DNF.lean`); snapshots, the reference-input schedule, `prevVisit`, the reconstruction functions, and the five locality statements (`CookLevin/Snapshot.lean`); `NPHard` transfer (flagged), Lemma 2.11 with the summit sketch (six clause families; acceptance as the local no-false-emission family; the emitting machine's clocked-schedule, trajectory-comparison, and unary-emission obligations), and Theorem 2.10 both halves (`CookLevin/Hardness.lean`); `coNPHard`/`coNPComplete` (flagged), `TAUTOLOGY` on the documented DNF fragment, and Example 2.21 (`ClassNP/Tautology.lean`). 14 definitions + 14 sorried statements, zero proofs; full **53-module fresh sweep** clean (exactly 59 admissions = 19 + 14 + 12 + 14); the eight Chapter-1 headline axiom prints admission-free; style lint zero campaign FAIL. **Phase-4 audit pack prepared** (`audits/ch2-phase4-{pack,bundle}.md`, 68 attachments incl. the order list) with the locality theorems' adversarial re-derivation and design questions (a)-(f) as priorities. With this phase, **all mandatory-core statements of the chapter are on the books**; the gate awaits `audits/ch2-phase4-findings.md`, after which the fill campaign (E1-E5) is next | Decided |

| Phase-4 audit round 1 (`audits/ch2-phase4-findings.md`, audited at `6484ce88`): **zero blockers, 1 major, 2 minors, 5 notes — gate stays open; all accepted.** No false definition or statement anywhere; all five locality theorems certified (Derivation A: the cell recurrence with the exhaustive optional-write table — including `some none` erasing to blank and writes on the halting transition, which the fill must preserve); the tableau correctness independently re-derived (Derivation B: exact-length normalization, packing injectivity, constant-arity Claim-2.13 templates with non-injective relabeling, the strong-induction bitwise-pinning argument — with the **product snapshot encoding** recommended so fields are literal slices); **design question (a) resolved affirmatively** (Derivation C: the no-false-emission family survives a seven-case adversarial table, the decider contract invoked exactly where needed); the DNF/TAUTOLOGY package fully verified incl. the malformed-`f(z)` branch (Derivation D; the DNF congruence bridge appropriate as a private fill lemma); questions (b)-(f) all affirmed. **The major**: the emitting-machine sketch omitted the output-isolation/halt-redirection contract for its preparatory stages — `timeConstructible_poly`'s machines answer on the real output tape and the reference simulation emits its verdict, so unwrapped forwarding yields the concrete false positive `[false] ++ serialize φ_x → fallback ∈ SAT` (the phase-1 enumerator lesson recurring at the emitter); the auditor supplied a six-stage silent-controller contract table. Minors: a quantifier slip in the TAUTOLOGY membership prose (a DNF is false iff **every** term fails); two missing precise imports in `Hardness.lean`. Notes adopted: the exact serialization-length identity as the fill ledger (the pinning family costs `n(n-1)/2 + 5n` bits, absorbed since `T ≥ (m+1)²`); the survey-row nuance ("un-auditable" = not audit-ready under this protocol as supplied; the effort comparison an engineering estimate not excluding partial-reuse strategies) | Decided |
| Phase-4 round-1 repairs executed (sketch/prose + two import lines — **no statement changed**): the `SAT_NPHard` emitting-machine sketch rewritten around the **output-silence contract** with the audit's six-stage table adopted verbatim (exact arithmetic with captured answers; virtual-input reference simulation; discarded source output with internal halted flag and frozen trajectory to `T`; trajectory recording; last-visit comparison; serialization with the empty-until-serialization output invariant), the product-encoding choice, and the exact length ledger; the TAUTOLOGY membership prose corrected to the every-term-fails quantifier; `Hardness.lean` gains the two precise imports (`ClassNP.TMSAT`, `Robustness.Oblivious` — the homes of the cited normalization theorems; both precede it in the order list, no cycles). Statement drift enumerated: 0 signatures, 0 definitions, 2 import lines (`Hardness.lean`); `Tautology.lean` comment-only (corrected stripper recipe). Repaired modules and facades re-gated; admissions unchanged (59). **Round-2 re-audit next** (protocol: no gate closes on a round reporting majors) | Decided |

| Phase-4 audit round 2 (`audits/ch2-phase4-reaudit-findings.md`, audited at `c3579472`): **zero blockers, zero majors, zero minors, 3 notes — gate condition met with nothing to sweep**, the campaign's cleanest round. Resolution table verified row by row; the six-stage output-silence transcription judged semantically faithful and the emitter obligation list **complete at statement-phase granularity** (stage-by-stage boundary checks; the round-1 counterexample re-fired against the repaired contract and confirmed closed); the product encoding matches Derivation B with no extra well-formedness family; the length/time ledger independently re-derived (exact serializer identity confirmed; `c ≥ 1` via `not_computesInTime_zero`; pinning cost absorbed by `T ≥ (m+1)²`; `O_M(T²) = poly(n)` total at sequential-scan rates). Notes adopted: both contract tables inherited verbatim into the E4 emitter fill brief; the exact identity is the fill's length ledger; evidence separation retained. **Phase-4 audit gate closed** (`audits/ch2-phase4-resolutions.md`). **All four Chapter-2 statement-phase gates are now closed** — 59 audited-true admissions (19 + 14 + 12 + 14); every mandatory-core statement of the chapter is on the books. Next: the fill campaign (E1-E5), beginning with epoch partitioning and briefs | Decided |

| Backlog consolidation (2026-09-18): the repository-level `backlog.md` created as the canonical tracking file — full human-review question bodies (CH1-Q1, CH1-Q2, CH2-Q1, moved verbatim; the plans keep stable numbered stubs that audit documents cite), the on-hold fill campaign with the audit-mandated fill-brief inheritance index, deferred formalizations across chapters 1-3 and the ch-6 bridge theorems, pending user decisions (ch-6 integration path among them), and housekeeping. `workflow.md` §1 points to it; it joins audit bundle attachment sets from the next round. Decision-log history stays in the plans, never moved | Decided |

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Ch. 2, pp. 38-67.)
